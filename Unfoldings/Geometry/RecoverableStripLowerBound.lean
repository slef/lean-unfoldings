module

public import Unfoldings.Geometry.MonotoneStripLowerBound
public import Unfoldings.Geometry.RecoverableStripInjective
public import Unfoldings.Topology.ClosureLowerBound

/-! Lower distance bounds cross coherent pinches and extend to all actual bank traces. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem lower_norm_bound_strict_of_core_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c : ℝ}
    (nonnegative : 0 ≤ c)
    (bounds : ∀ i, ConeCoordinateBound (A i) c 1 ∧ ConeCoordinateBound (A i) c (-1))
    (a b : ℝ) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, z ∈ S.coreCarrier → z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z)
    {p q : ℂ} (first : p ∈ S.strictCarrier ∧ p.re + p.im ∈ Set.Icc a b)
    (last : q ∈ S.strictCarrier ∧ q.re + q.im ∈ Set.Icc a b) :
    c * ‖q - p‖ ≤ 2 * ‖F q - F p‖ := by
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
      {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b} :=
    fun _ member => ⟨S.inset_subset_core εpositive member.1, member.2⟩
  exact (S.inset ε).lower_norm_bound_bounded_of_affine_selection A continuous nonnegative bounds a b
    (Fcontinuous.mono inside) (fun z member => selection z (inside member).1 (inside member).2)
    ⟨S.mem_inset (psmall.trans (min_le_left _ _)) (psmall.trans (min_le_right _ _)), first.2⟩
    ⟨S.mem_inset (qsmall.trans (min_le_left _ _)) (qsmall.trans (min_le_right _ _)), last.2⟩

theorem lower_norm_bound_strict_of_recoverable_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c : ℝ}
    (nonnegative : 0 ≤ c)
    (bounds : ∀ i, ConeCoordinateBound (A i) c 1 ∧ ConeCoordinateBound (A i) c (-1))
    (E : Set ℂ) (a b : ℝ) (pinches : S.RecoverablePinchesIn E a b) {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧
      z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z)
    {p q : ℂ} (first : p ∈ S.strictCarrier ∧ p.re + p.im ∈ Set.Icc a b)
    (last : q ∈ S.strictCarrier ∧ q.re + q.im ∈ Set.Icc a b) :
    c * ‖q - p‖ ≤ 2 * ‖F q - F p‖ := by
  let k := max (p.re + p.im) (q.re + q.im)
  have kb : k ≤ b := max_le first.2.2 last.2.2
  have positive_end : S.lower.coordinate k < S.upper.coordinate k := by
    rcases le_total (p.re + p.im) (q.re + q.im) with ordered | ordered
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_right ordered]
      exact last.1.1.trans last.1.2
    · change S.lower.coordinate (max _ _) < S.upper.coordinate (max _ _)
      rw [max_eq_left ordered]
      exact first.1.1.trans first.1.2
  have inside : {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a k} ⊆
      {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧ z.re + z.im ∈ Set.Icc a b} := by
    intro z member
    have slab : z.re + z.im ∈ Set.Icc a b := ⟨member.2.1, member.2.2.trans kb⟩
    refine ⟨?_, slab⟩
    rcases member.1.2 with strict | collapsed
    · exact Or.inl strict
    · have coherent := pinches _ slab collapsed k ⟨member.2.2, kb⟩ positive_end
      have point : S.lower.point (z.re + z.im) = z := S.lower.point_eq_of_coordinate z
        (le_antisymm member.1.1.1 (member.1.1.2.trans_eq collapsed.symm))
      exact Or.inr (point ▸ coherent)
  exact S.lower_norm_bound_strict_of_core_selection A continuous nonnegative bounds a k
    (Fcontinuous.mono inside)
    (fun z member slab => selection z (inside ⟨member, slab⟩).1 (inside ⟨member, slab⟩).2)
    ⟨first.1, first.2.1, le_max_left _ _⟩ ⟨last.1, last.2.1, le_max_right _ _⟩

/-- A continuous actual trace is injective on the full closure of the strict slab,
including all its approached bank points and its terminal pinch. -/
theorem injOn_closure_trace_of_recoverable_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j)
    (E : Set ℂ) (a b : ℝ) (pinches : S.RecoverablePinchesIn E a b) {F G : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | (z ∈ S.strictCarrier ∨ z ∈ E) ∧
      z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
      z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z)
    (Gcontinuous : Continuous G)
    (equal : Set.EqOn F G {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}) :
    Set.InjOn G (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}) := by
  obtain ⟨c, cpositive, bounds⟩ := exists_common_affine_cone_bound A positive
  apply injOn_closure_of_lower_norm_bound Gcontinuous (K := 2) cpositive
  intro p first q last
  have bound := S.lower_norm_bound_strict_of_recoverable_selection A continuous cpositive.le bounds
    E a b pinches Fcontinuous selection first last
  rwa [equal first, equal last] at bound

end Unfoldings.MonotoneStrip
