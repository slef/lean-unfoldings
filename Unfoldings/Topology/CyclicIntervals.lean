module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Abel

/-! Construct an oriented cyclic interval, including a path through all of its selected indices. -/

@[expose] public section

namespace Unfoldings

/-- A nonempty proper initial interval has precisely its two expected cyclic transitions. -/
theorem finRotate_initial_interval {n : ℕ} (k : Fin (n + 1)) (positive : 0 < k.val) :
    let last : Fin (n + 1) := ⟨k.val - 1, by omega⟩
    Fin.last n ≠ last ∧
      (¬ (Fin.last n).val < k.val ∧ (finRotate (n + 1) (Fin.last n)).val < k.val) ∧
      (last.val < k.val ∧ ¬ (finRotate (n + 1) last).val < k.val) ∧
      ∀ i : Fin (n + 1), i ≠ Fin.last n → i ≠ last →
        ((finRotate (n + 1) i).val < k.val ↔ i.val < k.val) := by
  let last : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  have next_last : finRotate (n + 1) last = k := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (by
      intro equal
      have values := congrArg Fin.val equal
      change k.val - 1 = n at values
      omega)]
    change k.val - 1 + 1 = k.val
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equal
    have values := congrArg Fin.val equal
    change n = k.val - 1 at values
    omega
  · rw [finRotate_last]
    exact ⟨by change ¬ n < k.val; omega, positive⟩
  · rw [next_last]
    exact ⟨by change k.val - 1 < k.val; omega, lt_irrefl _⟩
  · intro i not_last not_before
    rw [coe_finRotate_of_ne_last not_last]
    have values : i.val ≠ k.val - 1 := fun equal => not_before (Fin.ext equal)
    omega

/-- Select the forward arc from `start` up to but excluding `finish`.
The final clause gives an actual directed prefix inside the arc to each selected index. -/
theorem exists_finRotate_interval {n : ℕ} (start finish : Fin (n + 1))
    (different : start ≠ finish) :
    ∃ (region : Fin (n + 1) → Prop) (a b : Fin (n + 1)),
      a ≠ b ∧ finRotate (n + 1) a = start ∧ finRotate (n + 1) b = finish ∧
      (¬ region a ∧ region (finRotate (n + 1) a)) ∧
      (region b ∧ ¬ region (finRotate (n + 1) b)) ∧
      (∀ i, i ≠ a → i ≠ b → (region (finRotate (n + 1) i) ↔ region i)) ∧
      ∀ i, region i → ∃ m : ℕ, (finRotate (n + 1))^[m] start = i ∧
        ∀ j ≤ m, region ((finRotate (n + 1))^[j] start) := by
  let rotate := finCycle start
  let k : Fin (n + 1) := finish - start
  have positive : 0 < k.val := by
    by_contra zero
    have equal : k = 0 := by
      apply Fin.ext
      change k.val = 0
      omega
    have same : finish = start := sub_eq_zero.mp equal
    exact different same.symm
  let last : Fin (n + 1) := ⟨k.val - 1, by omega⟩
  have commute (i : Fin (n + 1)) : finRotate (n + 1) (rotate i) =
      rotate (finRotate (n + 1) i) := by
    simp only [finRotate_apply, rotate, finCycle_apply]
    abel
  have orbit (i : Fin (n + 1)) : (finRotate (n + 1))^[i.val] start = rotate i := by
    have formula := congrFun (finCycle_eq_finRotate_iterate (k := i)) start
    simpa only [rotate, finCycle_apply, add_comm] using formula.symm
  let region := fun i => (rotate.symm i).val < k.val
  obtain ⟨distinct, enters, leaves, stable⟩ := finRotate_initial_interval k positive
  refine ⟨region, rotate (Fin.last n), rotate last, rotate.injective.ne distinct, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [commute, finRotate_last]
    change (0 : Fin (n + 1)) + start = start
    exact zero_add _
  · rw [commute]
    have next_last : finRotate (n + 1) last = k := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (fun equal => distinct equal.symm)]
      change k.val - 1 + 1 = k.val
      omega
    rw [next_last]
    change (finish - start) + start = finish
    exact sub_add_cancel _ _
  · simpa only [region, commute, rotate.symm_apply_apply] using enters
  · simpa only [region, commute, rotate.symm_apply_apply] using leaves
  · intro i not_first not_last
    have formula := commute (rotate.symm i)
    rw [rotate.apply_symm_apply] at formula
    change (rotate.symm (finRotate (n + 1) i)).val < k.val ↔ (rotate.symm i).val < k.val
    rw [formula, rotate.symm_apply_apply]
    exact stable _ (fun equal => not_first (rotate.symm_apply_eq.mp equal))
      (fun equal => not_last (rotate.symm_apply_eq.mp equal))
  · intro i member
    refine ⟨(rotate.symm i).val, (orbit _).trans (rotate.apply_symm_apply i), ?_⟩
    intro j before
    have bounded : j < n + 1 := before.trans_lt (rotate.symm i).isLt
    rw [orbit ⟨j, bounded⟩]
    change (rotate.symm (rotate ⟨j, bounded⟩)).val < k.val
    rw [rotate.symm_apply_apply]
    exact before.trans_lt member

end Unfoldings
