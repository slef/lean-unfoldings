module

public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Unfoldings.Geometry.MonotoneStripBoundedInjective

/-! Injectivity inside open strip components does not require identifying coincident banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace MonotoneHeightGraph

def shift (G : MonotoneHeightGraph) (ε : ℝ) : MonotoneHeightGraph where
  coordinate h := G.coordinate h + ε
  coordinate_mono := by
    intro a b ordered
    have bound := G.coordinate_mono ordered
    dsimp only
    linarith
  complement_mono := by
    intro a b ordered
    have bound := G.complement_mono ordered
    dsimp only
    linarith

end MonotoneHeightGraph

namespace MonotoneStrip

variable (S : MonotoneStrip)

/-- Clamp offset boundaries toward the middle. They remain ordered even at zero-width tails. -/
def inset (ε : ℝ) : MonotoneStrip :=
  let middle := S.lower.average S.upper
  ⟨(S.lower.shift ε).min middle, (S.upper.shift (-ε)).max middle,
    fun _ => (min_le_right _ _).trans (le_max_right _ _)⟩

theorem inset_strict_subset {ε h : ℝ} (positive : 0 < ε)
    (width : S.lower.coordinate h < S.upper.coordinate h) {z : ℂ}
    (height : z.re + z.im = h) (member : z ∈ (S.inset ε).carrier) :
    z ∈ S.strictCarrier := by
  change Min.min (S.lower.coordinate (z.re + z.im) + ε)
      ((S.lower.coordinate (z.re + z.im) + S.upper.coordinate (z.re + z.im)) / 2) ≤ z.re ∧
    z.re ≤ Max.max (S.upper.coordinate (z.re + z.im) + -ε)
      ((S.lower.coordinate (z.re + z.im) + S.upper.coordinate (z.re + z.im)) / 2) at member
  rw [height] at member
  have lower : S.lower.coordinate h < Min.min (S.lower.coordinate h + ε)
      ((S.lower.coordinate h + S.upper.coordinate h) / 2) :=
    lt_min (by linarith) (by linarith)
  have upper : Max.max (S.upper.coordinate h + -ε)
      ((S.lower.coordinate h + S.upper.coordinate h) / 2) < S.upper.coordinate h :=
    max_lt (by linarith) (by linarith)
  change S.lower.coordinate (z.re + z.im) < z.re ∧ z.re < S.upper.coordinate (z.re + z.im)
  rw [height]
  exact ⟨lower.trans_le member.1, member.2.trans_lt upper⟩

theorem mem_inset {ε : ℝ} {z : ℂ}
    (lower : ε ≤ z.re - S.lower.coordinate (z.re + z.im))
    (upper : ε ≤ S.upper.coordinate (z.re + z.im) - z.re) :
    z ∈ (S.inset ε).carrier := by
  constructor
  · change Min.min (S.lower.coordinate (z.re + z.im) + ε) _ ≤ z.re
    exact (min_le_left _ _).trans (by linarith)
  · change z.re ≤ Max.max (S.upper.coordinate (z.re + z.im) + -ε) _
    exact (show z.re ≤ S.upper.coordinate (z.re + z.im) + -ε by linarith).trans
      (le_max_left _ _)

/-- Work on a slab of positive width. An inset closed strip contains any given two interior
points and stays strictly inside, so the existing closed-strip theorem applies. No values on
the cut banks, and no extension through a zero-width tail, are needed. -/
theorem injOn_strict_of_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j) (a b : ℝ)
    (width : ∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h)
    {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, z ∈ S.strictCarrier → z.re + z.im ∈ Set.Icc a b →
      ∃ i, F z = A i z) :
    Set.InjOn F {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  intro p first q last equal
  let pl := p.re - S.lower.coordinate (p.re + p.im)
  let pu := S.upper.coordinate (p.re + p.im) - p.re
  let ql := q.re - S.lower.coordinate (q.re + q.im)
  let qu := S.upper.coordinate (q.re + q.im) - q.re
  have gap : 0 < min (min pl pu) (min ql qu) :=
    lt_min (lt_min (sub_pos.mpr first.1.1) (sub_pos.mpr first.1.2))
      (lt_min (sub_pos.mpr last.1.1) (sub_pos.mpr last.1.2))
  obtain ⟨ε, εpositive, εsmall⟩ := exists_between gap
  have psmall : ε ≤ min pl pu := εsmall.le.trans (min_le_left _ _)
  have qsmall : ε ≤ min ql qu := εsmall.le.trans (min_le_right _ _)
  have inside : (S.inset ε).boundedCarrier a b ⊆
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
    intro z member
    exact ⟨S.inset_strict_subset εpositive (width _ member.2) rfl member.1, member.2⟩
  have injective := (S.inset ε).injOn_bounded_of_affine_selection A continuous positive a b
    (Fcontinuous.mono inside) (fun z member => selection z (inside member).1 (inside member).2)
  exact injective
    ⟨S.mem_inset (psmall.trans (min_le_left _ _)) (psmall.trans (min_le_right _ _)), first.2⟩
    ⟨S.mem_inset (qsmall.trans (min_le_left _ _)) (qsmall.trans (min_le_right _ _)), last.2⟩ equal

end MonotoneStrip
end Unfoldings
