module

public import Unfoldings.Geometry.MonotoneStripOpenInjective

/-! Inset strips can cross pinches when their common point has a coherent map value. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

/-- Include pinches while excluding both distinct banks of a positive-width strip. -/
def coreCarrier : Set ℂ :=
  {z | z ∈ S.carrier ∧ (z ∈ S.strictCarrier ∨
    S.lower.coordinate (z.re + z.im) = S.upper.coordinate (z.re + z.im))}

theorem inset_subset {ε : ℝ} (nonnegative : 0 ≤ ε) : (S.inset ε).carrier ⊆ S.carrier := by
  intro z member
  have lower : S.lower.coordinate (z.re + z.im) ≤
      Min.min (S.lower.coordinate (z.re + z.im) + ε)
        ((S.lower.coordinate (z.re + z.im) + S.upper.coordinate (z.re + z.im)) / 2) :=
    le_min (by linarith) (by linarith [S.ordered (z.re + z.im)])
  have upper : Max.max (S.upper.coordinate (z.re + z.im) + -ε)
      ((S.lower.coordinate (z.re + z.im) + S.upper.coordinate (z.re + z.im)) / 2) ≤
        S.upper.coordinate (z.re + z.im) :=
    max_le (by linarith) (by linarith [S.ordered (z.re + z.im)])
  exact ⟨lower.trans member.1, member.2.trans upper⟩

theorem inset_subset_core {ε : ℝ} (positive : 0 < ε) :
    (S.inset ε).carrier ⊆ S.coreCarrier := by
  intro z member
  refine ⟨S.inset_subset positive.le member, ?_⟩
  by_cases width : S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im)
  · exact Or.inl (S.inset_strict_subset positive width rfl member)
  · exact Or.inr (le_antisymm (S.ordered _) (le_of_not_gt width))

/-- A map continuous on the core cannot overlap across a pinch either. The value at that
pinch must really be coherent; no equality of distinct bank values is inferred from projection. -/
theorem injOn_strict_of_core_affine_selection {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (positive : ∀ i j, 0 < affineAxisMargins (A i) j) (a b : ℝ)
    {F : ℂ → ℂ}
    (Fcontinuous : ContinuousOn F {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b})
    (selection : ∀ z, z ∈ S.coreCarrier → z.re + z.im ∈ Set.Icc a b → ∃ i, F z = A i z) :
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
      {z | z ∈ S.coreCarrier ∧ z.re + z.im ∈ Set.Icc a b} :=
    fun _ member => ⟨S.inset_subset_core εpositive member.1, member.2⟩
  have injective := (S.inset ε).injOn_bounded_of_affine_selection A continuous positive a b
    (Fcontinuous.mono inside) (fun z member => selection z (inside member).1 (inside member).2)
  exact injective
    ⟨S.mem_inset (psmall.trans (min_le_left _ _)) (psmall.trans (min_le_right _ _)), first.2⟩
    ⟨S.mem_inset (qsmall.trans (min_le_left _ _)) (qsmall.trans (min_le_right _ _)), last.2⟩ equal

end Unfoldings.MonotoneStrip
