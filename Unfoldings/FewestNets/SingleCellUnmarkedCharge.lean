module

public import Unfoldings.FewestNets.SingleCellCyclicCharge

/-! The signed cyclic charge counts only unmarked changes in its pointwise upper bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SingleCellCharge

variable {m : ℕ}

/-- The two marked sides may share a vertex, so their endpoints retain
multiplicity while the actual sides are removed from the crossing sum. -/
theorem cycleCharge_le_unmarked (label : Fin (m + 1) → Bool) {first second : Fin (m + 1)}
    (distinct : first ≠ second) :
    cycleCharge label first second ≤
      (∑ i ∈ (Finset.univ.erase first).erase second,
        crossing (label i, label (finRotate (m + 1) i))) / 4 := by
  classical
  let value (i : Fin (m + 1)) := crossing (label i, label (finRotate (m + 1) i))
  let unmarked := (Finset.univ.erase first).erase second
  change cycleCharge label first second ≤ (∑ i ∈ unmarked, value i) / 4
  by_cases homogeneous : ∀ i, label i = true
  · have value_zero (i : Fin (m + 1)) : value i = 0 := by
      simp only [value, crossing, homogeneous, ↓reduceIte]
    have charge_zero : cycleCharge label first second = 0 := by
      have all : label = fun _ => true := funext homogeneous
      rw [all]
      norm_num [cycleCharge, crossing, charge, endpoints]
    simp only [charge_zero, value_zero, Finset.sum_const_zero, zero_div, le_refl]
  · have kept : second ∈ (Finset.univ.erase first : Finset (Fin (m + 1))) :=
      Finset.mem_erase.mpr ⟨distinct.symm, Finset.mem_univ _⟩
    have step₀ := Finset.sum_erase_add Finset.univ value (Finset.mem_univ first)
    have step₁ := Finset.sum_erase_add (Finset.univ.erase first) value kept
    have total : (∑ i, value i) = (∑ i ∈ unmarked, value i) + value first + value second := by
      change (∑ i ∈ unmarked, value i) + value second = _ at step₁
      linarith only [step₀, step₁]
    unfold cycleCharge
    change charge (∑ i, value i) (label first, label (finRotate (m + 1) first))
      (label second, label (finRotate (m + 1) second)) _ ≤ _
    rw [total, decide_eq_false homogeneous]
    exact charge_le_unmarked _ _ _

/-- A degenerate normal polygon with no unmarked changes contributes a nonpositive charge. -/
theorem cycleCharge_nonpos_of_no_unmarked_change (label : Fin (m + 1) → Bool)
    {first second : Fin (m + 1)} (distinct : first ≠ second)
    (unchanged : ∀ i ≠ first, i ≠ second → label i = label (finRotate (m + 1) i)) :
    cycleCharge label first second ≤ 0 := by
  apply (cycleCharge_le_unmarked label distinct).trans_eq
  rw [div_eq_zero_iff]
  left
  apply Finset.sum_eq_zero
  intro i hi
  have b := Finset.mem_erase.mp hi
  simp [crossing, unchanged i (Finset.mem_erase.mp b.2).1 b.1]

end Unfoldings.FewestNets.SingleCellCharge
