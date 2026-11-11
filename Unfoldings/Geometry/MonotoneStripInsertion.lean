module

public import Unfoldings.Geometry.MonotoneStripInterior
public import Unfoldings.Geometry.HeightGraphSplice

/-! Insert a strict internal source-to-target connector and continue along a specified tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

def insertionGraph (p : ℂ) (member : p ∈ S.carrier) (tail : MonotoneHeightGraph)
    (at_target : tail.coordinate (p.re + p.im) = p.re) : MonotoneHeightGraph :=
  let clipped := S.lower.clamp S.upper tail
  (S.interiorConnector p).splice clipped (p.re + p.im) (by
    rw [S.interiorConnector_target member]
    have lower : S.lower.coordinate (p.re + p.im) ≤ tail.coordinate (p.re + p.im) := by
      rw [at_target]
      exact member.1
    have upper : tail.coordinate (p.re + p.im) ≤ S.upper.coordinate (p.re + p.im) := by
      rw [at_target]
      exact member.2
    exact ((S.lower.clamp_eq S.upper tail lower upper).trans at_target).symm)

theorem insertionGraph_bounds (p : ℂ) (member : p ∈ S.carrier) (tail : MonotoneHeightGraph)
    (at_target : tail.coordinate (p.re + p.im) = p.re) (h : ℝ) :
    S.lower.coordinate h ≤ (S.insertionGraph p member tail at_target).coordinate h ∧
      (S.insertionGraph p member tail at_target).coordinate h ≤ S.upper.coordinate h := by
  by_cases before : h ≤ p.re + p.im
  · simp only [insertionGraph, MonotoneHeightGraph.splice, ite_eq_left before]
    exact S.interiorConnector_bounds member before
  · simp only [insertionGraph, MonotoneHeightGraph.splice, ite_eq_right before]
    exact S.lower.clamp_mem S.upper tail S.ordered h

theorem insertionGraph_strict_before (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    (lower_target : S.lower.coordinate (p.re + p.im) < p.re)
    (upper_target : p.re < S.upper.coordinate (p.re + p.im)) {h : ℝ}
    (before : h ≤ p.re + p.im) (width : S.lower.coordinate h < S.upper.coordinate h) :
    S.lower.coordinate h < (S.insertionGraph p member tail at_target).coordinate h ∧
      (S.insertionGraph p member tail at_target).coordinate h < S.upper.coordinate h := by
  simp only [insertionGraph, MonotoneHeightGraph.splice, ite_eq_left before]
  exact S.interiorConnector_strict lower_target upper_target before width

/-- An existing geometric tail is preserved at every height where it lies in the old strip. -/
theorem insertionGraph_preserves_tail (p : ℂ) (member : p ∈ S.carrier)
    (tail : MonotoneHeightGraph) (at_target : tail.coordinate (p.re + p.im) = p.re)
    {h : ℝ} (after : p.re + p.im ≤ h)
    (lower : S.lower.coordinate h ≤ tail.coordinate h)
    (upper : tail.coordinate h ≤ S.upper.coordinate h) :
    (S.insertionGraph p member tail at_target).coordinate h = tail.coordinate h := by
  by_cases same : h = p.re + p.im
  · subst h
    simp only [insertionGraph, MonotoneHeightGraph.splice, le_refl, ite_true]
    exact (S.interiorConnector_target member).trans at_target.symm
  · have before : ¬ h ≤ p.re + p.im := fun before => same (le_antisymm before after)
    simp only [insertionGraph, MonotoneHeightGraph.splice, ite_eq_right before]
    exact S.lower.clamp_eq S.upper tail lower upper

def lowerSplit (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h) : MonotoneStrip :=
  ⟨S.lower, G, fun h => (bounds h).1⟩

def upperSplit (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h) : MonotoneStrip :=
  ⟨G, S.upper, fun h => (bounds h).2⟩

theorem split_cover (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h) :
    (S.lowerSplit G bounds).carrier ∪ (S.upperSplit G bounds).carrier = S.carrier := by
  ext z
  constructor
  · rintro (first | last)
    · exact ⟨first.1, first.2.trans (bounds _).2⟩
    · exact ⟨(bounds _).1.trans last.1, last.2⟩
  · intro member
    rcases le_total z.re (G.coordinate (z.re + z.im)) with left | right
    · exact Or.inl ⟨member.1, left⟩
    · exact Or.inr ⟨right, member.2⟩

/-- The two substrip carriers share exactly their new monotone boundary, including contacts. -/
theorem split_intersection (G : MonotoneHeightGraph)
    (bounds : ∀ h, S.lower.coordinate h ≤ G.coordinate h ∧
      G.coordinate h ≤ S.upper.coordinate h) :
    (S.lowerSplit G bounds).carrier ∩ (S.upperSplit G bounds).carrier = Set.range G.point := by
  ext z
  constructor
  · rintro ⟨first, last⟩
    exact ⟨z.re + z.im, G.point_eq_of_coordinate z (le_antisymm last.1 first.2)⟩
  · rintro ⟨h, rfl⟩
    have height := G.point_height h
    change (S.lower.coordinate ((G.point h).re + (G.point h).im) ≤ (G.point h).re ∧
      (G.point h).re ≤ G.coordinate ((G.point h).re + (G.point h).im)) ∧
      (G.coordinate ((G.point h).re + (G.point h).im) ≤ (G.point h).re ∧
        (G.point h).re ≤ S.upper.coordinate ((G.point h).re + (G.point h).im))
    rw [height]
    exact ⟨⟨(bounds h).1, le_rfl⟩, ⟨le_rfl, (bounds h).2⟩⟩

end Unfoldings.MonotoneStrip
