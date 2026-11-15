module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-! A cyclic region avoiding the starting index is one ordinary contiguous interval. -/

@[expose] public section

namespace Unfoldings

/-- One entry and one exit, with the starting point outside, determine the whole region
in the ordinary linear order. In particular no later traversal can reenter that region. -/
theorem finRotate_two_exits_linear_interval {n : ℕ} (inside : Fin (n + 1) → Prop)
    (enter leave : Fin (n + 1))
    (enters : ¬ inside enter ∧ inside (finRotate (n + 1) enter))
    (leaves : inside leave ∧ ¬ inside (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ enter → i ≠ leave →
      (inside (finRotate (n + 1) i) ↔ inside i))
    (outside : ¬ inside 0) :
    enter.val < leave.val ∧ ∀ i, inside i ↔ enter.val < i.val ∧ i.val ≤ leave.val := by
  have before_enter (i : Fin (n + 1)) : i.val ≤ enter.val → ¬ inside i := by
    induction i using Fin.induction with
    | zero => exact fun _ => outside
    | succ k ih =>
      intro before member
      have not_enter : k.castSucc ≠ enter := by
        intro same
        have values := congrArg Fin.val same
        simp only [Fin.val_castSucc] at values
        simp only [Fin.val_succ] at before
        omega
      have next : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
      by_cases at_leave : k.castSucc = leave
      · apply leaves.2
        rw [← at_leave, next]
        exact member
      · apply ih (by simp only [Fin.val_succ, Fin.val_castSucc] at before ⊢; omega)
        exact (stable k.castSucc not_enter at_leave).mp (next.symm ▸ member)
  have ordered : enter.val < leave.val := by
    by_contra unordered
    exact before_enter leave (le_of_not_gt unordered) leaves.1
  refine ⟨ordered, fun i => ?_⟩
  induction i using Fin.induction with
  | zero =>
    exact iff_of_false outside (by
      simp only [Fin.val_zero, Nat.not_lt_zero, false_and, not_false_eq_true])
  | succ k ih =>
    have next : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
    by_cases at_enter : k.castSucc = enter
    · have yes : inside k.succ := by simpa only [← at_enter, next] using enters.2
      apply iff_of_true yes
      have values := congrArg Fin.val at_enter
      simp only [Fin.val_castSucc] at values
      simp only [Fin.val_succ]
      omega
    · by_cases at_leave : k.castSucc = leave
      · have no : ¬ inside k.succ := by simpa only [← at_leave, next] using leaves.2
        apply iff_of_false no
        have values := congrArg Fin.val at_leave
        simp only [Fin.val_castSucc] at values
        simp only [Fin.val_succ]
        omega
      · rw [← next, stable k.castSucc at_enter at_leave, ih]
        have not_first : k.val ≠ enter.val := fun equal => at_enter (Fin.ext equal)
        have not_last : k.val ≠ leave.val := fun equal => at_leave (Fin.ext equal)
        rw [next]
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega

end Unfoldings
