module

public import Unfoldings.Geometry.MonotoneStripLipschitz
public import Unfoldings.Geometry.MonotoneStripCore
public import Unfoldings.Geometry.RecoverableStripPinches

/-! Uniform strip bounds extend to strict interiors across all coherent reopening pinches. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem lipschitzOnWith_strict_of_core_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) (K : ℝ≥0)
    (linear_bound : ∀ i z, ‖(A i).linear z‖ ≤ K * ‖z‖) (a b : ℝ) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, z ∈ S.coreCarrier → z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z) :
    LipschitzOnWith (4 * K) F {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p first q last
  let pl := p.re - S.lower.coordinate (p.re + p.im)
  let pu := S.upper.coordinate (p.re + p.im) - p.re
  let ql := q.re - S.lower.coordinate (q.re + q.im)
  let qu := S.upper.coordinate (q.re + q.im) - q.re
  have gap : 0 < min (min pl pu) (min ql qu) :=
    lt_min (lt_min (sub_pos.mpr first.1.1) (sub_pos.mpr first.1.2))
      (lt_min (sub_pos.mpr last.1.1) (sub_pos.mpr last.1.2))
  obtain ⟨ε, positive, small⟩ := exists_between gap
  have psmall : ε ≤ min pl pu := small.le.trans (min_le_left _ _)
  have qsmall : ε ≤ min ql qu := small.le.trans (min_le_right _ _)
  have inside : (S.inset ε).boundedCarrier a b ⊆
      {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b} :=
    fun _ member => ⟨S.inset_subset_core positive member.1, member.2⟩
  have bound := (S.inset ε).lipschitzOnWith_bounded_of_affine_selection A continuous K linear_bound
    a b (Fcontinuous.mono inside)
    (fun z member => selection z (inside member).1 (inside member).2)
  exact bound.dist_le_mul p
    ⟨S.mem_inset (psmall.trans (min_le_left _ _)) (psmall.trans (min_le_right _ _)), first.2⟩ q
    ⟨S.mem_inset (qsmall.trans (min_le_left _ _)) (qsmall.trans (min_le_right _ _)), last.2⟩

theorem lipschitzOnWith_strict_of_recoverable_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) (K : ℝ≥0)
    (linear_bound : ∀ i z, ‖(A i).linear z‖ ≤ K * ‖z‖) (E : Set ℂ) (a b : ℝ)
    (pinches : S.RecoverablePinchesIn E a b) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧
      z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z) :
    LipschitzOnWith (4 * K) F {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  let c := max (p.re + p.im) (q.re + q.im)
  have cb : c ≤ b := max_le hp.2.2 hq.2.2
  have positive_end : S.lower.coordinate c < S.upper.coordinate c := by
    rcases le_total (p.re + p.im) (q.re + q.im) with ordered | ordered
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_right ordered]
      exact hq.1.1.trans hq.1.2
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_left ordered]
      exact hp.1.1.trans hp.1.2
  have inside : {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a c} ⊆
      {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧ z.re + z.im ∈ Set.Icc a b} := by
    intro z member
    have slab : z.re + z.im ∈ Set.Icc a b := ⟨member.2.1, member.2.2.trans cb⟩
    refine ⟨?_, slab⟩
    rcases member.1.2 with strict | collapsed
    · exact Or.inl strict
    · have coherent := pinches _ slab collapsed c ⟨member.2.2, cb⟩ positive_end
      have point : S.lower.point (z.re + z.im) = z := S.lower.point_eq_of_coordinate z
        (le_antisymm member.1.1.1 (member.1.1.2.trans_eq collapsed.symm))
      exact Or.inr (point ▸ coherent)
  have bound := S.lipschitzOnWith_strict_of_core_selection A continuous K linear_bound a c
    (Fcontinuous.mono inside)
    (fun z member slab => selection z (inside ⟨member, slab⟩).1 (inside ⟨member, slab⟩).2)
  exact bound.dist_le_mul p ⟨hp.1, hp.2.1, le_max_left _ _⟩ q
    ⟨hq.1, hq.2.1, le_max_right _ _⟩

end Unfoldings.MonotoneStrip
