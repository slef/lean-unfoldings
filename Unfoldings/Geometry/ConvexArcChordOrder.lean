module

public import Unfoldings.Combinatorics.CyclicAdjacentRemoval
public import Unfoldings.Geometry.StrictConvexChordOrder
public import Mathlib.Topology.Order.IntermediateValue

/-! Chords joining consecutive endpoints of convex boundary arcs have one consistent orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings

attribute [local instance] Complex.finrank_real_complex_fact

variable {n : ℕ} (p : Fin (n + 1) → ℂ)

/-- The signed area of the chord and the ray from its first endpoint. -/
def chordSide (i : Fin (n + 1)) (z : ℂ) : ℝ :=
  Complex.orientation.areaForm (p (finRotate (n + 1) i) - p i) (z - p i)

private theorem chordSide_at_next (i : Fin (n + 1)) :
    chordSide p i (p (finRotate (n + 1) i)) = 0 :=
  Complex.orientation.areaForm_apply_self _

private theorem chordSide_at_self (i : Fin (n + 1)) : chordSide p i (p i) = 0 := by
  simp [chordSide]

private theorem chordSide_at_following (i : Fin (n + 1)) :
    chordSide p i (p (finRotate (n + 1) (finRotate (n + 1) i))) =
      chordSide p (finRotate (n + 1) i) (p i) := by
  let j := finRotate (n + 1) i
  let k := finRotate (n + 1) j
  let u := p j - p i
  let v := p k - p j
  change Complex.orientation.areaForm u (p k - p i) =
    Complex.orientation.areaForm v (p i - p j)
  rw [show p k - p i = v + u by dsimp [u, v]; abel, map_add,
    Complex.orientation.areaForm_apply_self, add_zero, show p i - p j = -u by
      dsimp [u]; abel, map_neg]
  exact Complex.orientation.areaForm_swap u v

private theorem positive_iff_of_preconnected_nonzero {S : Set ℂ}
    (connected : IsPreconnected S) {f : ℂ → ℝ} (continuous : Continuous f)
    (nonzero : ∀ z ∈ S, f z ≠ 0) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    0 < f x ↔ 0 < f y := by
  have images := (connected.image f continuous.continuousOn).ordConnected
  have from_x : f x ∈ f '' S := Set.mem_image_of_mem f hx
  have from_y : f y ∈ f '' S := Set.mem_image_of_mem f hy
  have zero_avoided : 0 ∉ f '' S := by
    rintro ⟨z, hz, hz'⟩
    exact nonzero z hz hz'
  refine ⟨fun pos => ?_, fun pos => ?_⟩
  · by_contra negative
    exact zero_avoided (images.out from_y from_x ⟨le_of_not_gt negative, pos.le⟩)
  · by_contra negative
    exact zero_avoided (images.out from_x from_y ⟨le_of_not_gt negative, pos.le⟩)

/-- If a strictly convex boundary is traversed by consecutive arcs, each
inscribed chord has all the other vertices on the same open side. -/
theorem chordSide_positive_iff_of_boundary_arcs {K : Set ℂ} (closed : IsClosed K)
    (strict : StrictConvex ℝ K) (large : 3 ≤ n + 1)
    (point : ∀ i, p i ∈ frontier K) (injective : Function.Injective p)
    (edge : Fin (n + 1) → Set ℂ) (connected : ∀ i, IsPreconnected (edge i))
    (boundary : ∀ i, edge i ⊆ frontier K)
    (incidence : ∀ i j, p j ∈ edge i ↔ j = i ∨ j = finRotate (n + 1) i)
    (i : Fin (n + 1)) {j k : Fin (n + 1)}
    (ji : j ≠ i) (jnext : j ≠ finRotate (n + 1) i)
    (ki : k ≠ i) (knext : k ≠ finRotate (n + 1) i) :
    0 < chordSide p i (p j) ↔ 0 < chordSide p i (p k) := by
  let next := finRotate (n + 1)
  let sign (j : Fin (n + 1)) := 0 < chordSide p i (p j)
  have continuous : Continuous (chordSide p i) := by
    apply LinearMap.continuous_of_finiteDimensional
      (Complex.orientation.areaForm (p (next i) - p i)) |>.comp
    exact continuous_id.sub continuous_const
  have unequal : p i ≠ p (next i) := injective.ne (Ne.symm (finRotate_ne_of_three_le large i))
  have along (l : Fin (n + 1)) (li : l ≠ i) (lb : l ≠ next i)
      (first : next l ≠ i) (second : next l ≠ next i) : sign l = sign (next l) := by
    have never_zero (z : ℂ) (hz : z ∈ edge l) : chordSide p i z ≠ 0 := by
      apply areaForm_chord_ne_zero_of_frontier closed strict (point _) (point _) (boundary l hz)
        unequal
      · intro same
        rw [← same] at hz
        rcases (incidence _ _).mp hz with eq | eq
        · exact li eq.symm
        · exact first eq.symm
      · intro same
        rw [← same] at hz
        rcases (incidence _ _).mp hz with eq | eq
        · exact lb eq.symm
        · exact second eq.symm
    exact propext (positive_iff_of_preconnected_nonzero (connected l) continuous never_zero
      ((incidence _ _).mpr (Or.inl rfl)) ((incidence _ _).mpr (Or.inr rfl)))
  exact Iff.of_eq (eq_of_finRotate_invariant_away_from_pair large sign i along ji jnext ki knext)

/-- The chords around a strictly convex boundary make consistently signed turns.
All vertices lie on the inward side of each directed chord. -/
theorem convex_arc_chord_orientation {K : Set ℂ} (closed : IsClosed K)
    (strict : StrictConvex ℝ K) (large : 3 ≤ n + 1)
    (point : ∀ i, p i ∈ frontier K) (injective : Function.Injective p)
    (edge : Fin (n + 1) → Set ℂ) (connected : ∀ i, IsPreconnected (edge i))
    (boundary : ∀ i, edge i ⊆ frontier K)
    (incidence : ∀ i j, p j ∈ edge i ↔ j = i ∨ j = finRotate (n + 1) i) :
    (∀ i j, 0 ≤ chordSide p i (p j)) ∧
      (∀ i, 0 < chordSide p i (p (finRotate (n + 1) (finRotate (n + 1) i)))) ∨
    (∀ i j, chordSide p i (p j) ≤ 0) ∧
      (∀ i, chordSide p i (p (finRotate (n + 1) (finRotate (n + 1) i))) < 0) := by
  let next := finRotate (n + 1)
  let side (i : Fin (n + 1)) := 0 < chordSide p i (p (next (next i)))
  have step_ne (i : Fin (n + 1)) : next i ≠ i := finRotate_ne_of_three_le large i
  have two_ne (i : Fin (n + 1)) : next (next i) ≠ i := finRotate_twice_ne_of_three_le large i
  have match_side (i : Fin (n + 1)) : side i = side (next i) := by
    apply propext
    change (0 < chordSide p i (p (next (next i)))) ↔ _
    rw [chordSide_at_following]
    exact chordSide_positive_iff_of_boundary_arcs p closed strict large point injective
      edge connected boundary incidence (next i) (Ne.symm (step_ne i)) (Ne.symm (two_ne i))
      (two_ne (next i)) (step_ne (next (next i)))
  have same (i : Fin (n + 1)) : side i = side 0 :=
    eq_of_finRotate_invariant side match_side i 0
  have not_zero (i j : Fin (n + 1)) (ji : j ≠ i) (jn : j ≠ next i) :
      chordSide p i (p j) ≠ 0 :=
    areaForm_chord_ne_zero_of_frontier closed strict (point _) (point _) (point _)
      (injective.ne (Ne.symm (step_ne _))) (injective.ne (Ne.symm ji)) (injective.ne (Ne.symm jn))
  have sign_match (i j : Fin (n + 1)) (ji : j ≠ i) (jn : j ≠ next i) :
      (0 < chordSide p i (p j)) ↔ side i :=
    chordSide_positive_iff_of_boundary_arcs p closed strict large point injective
      edge connected boundary incidence i ji jn (two_ne i) (step_ne (next i))
  by_cases pos : side 0
  · have sides (i : Fin (n + 1)) : side i := (same i).symm ▸ pos
    refine Or.inl ⟨fun i j => ?_, sides⟩
    by_cases ji : j = i
    · rw [ji, chordSide_at_self]
    · by_cases jn : j = next i
      · rw [jn, chordSide_at_next]
      · exact ((sign_match i j ji jn).mpr (sides i)).le
  · have sides (i : Fin (n + 1)) : ¬ side i := fun h => pos ((same i) ▸ h)
    refine Or.inr ⟨fun i j => ?_, fun i => ?_⟩
    · by_cases ji : j = i
      · rw [ji, chordSide_at_self]
      · by_cases jn : j = next i
        · rw [jn, chordSide_at_next]
        · exact le_of_not_gt (fun h => sides i ((sign_match i j ji jn).mp h))
    · exact lt_of_le_of_ne (le_of_not_gt (sides i))
        (not_zero i (next (next i)) (two_ne i) (step_ne (next i)))

end Unfoldings
