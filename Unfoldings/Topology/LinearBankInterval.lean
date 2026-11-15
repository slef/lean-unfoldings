module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Concrete nonwrapping bank intervals and their actual cyclic transitions. -/

@[expose] public section

namespace Unfoldings

/-- The banks strictly between two separated positions form a cyclic region whose endpoint
vertices are exactly the successor of the first position and the second position. -/
theorem finRotate_open_bank_interval {n : ℕ} (a finish : Fin (n + 1))
    (separated : a.val + 1 < finish.val) :
    ∃ b : Fin (n + 1), b.val + 1 = finish.val ∧
      finRotate (n + 1) b = finish ∧ a ≠ b ∧
      (¬ (a.val < a.val ∧ a.val < finish.val) ∧
        (a.val < (finRotate (n + 1) a).val ∧ (finRotate (n + 1) a).val < finish.val)) ∧
      ((a.val < b.val ∧ b.val < finish.val) ∧
        ¬ (a.val < (finRotate (n + 1) b).val ∧ (finRotate (n + 1) b).val < finish.val)) ∧
      ∀ i : Fin (n + 1), i ≠ a → i ≠ b →
        ((a.val < (finRotate (n + 1) i).val ∧ (finRotate (n + 1) i).val < finish.val) ↔
          (a.val < i.val ∧ i.val < finish.val)) := by
  let b : Fin (n + 1) := ⟨finish.val - 1, by omega⟩
  have a_not_last : a ≠ Fin.last n := by
    intro same
    have values := congrArg Fin.val same
    simp only [Fin.val_last] at values
    omega
  have b_not_last : b ≠ Fin.last n := by
    intro same
    have values := congrArg Fin.val same
    change finish.val - 1 = n at values
    omega
  have next_b : finRotate (n + 1) b = finish := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last b_not_last]
    dsimp only [b]
    omega
  refine ⟨b, by dsimp [b]; omega, next_b, ?_, ?_, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val same
    change a.val = finish.val - 1 at values
    omega
  · rw [coe_finRotate_of_ne_last a_not_last]
    omega
  · rw [next_b]
    dsimp only [b]
    omega
  · intro i not_a not_b
    by_cases last : i = Fin.last n
    · rw [last, finRotate_last]
      simp only [Fin.val_zero, Fin.val_last]
      omega
    · rw [coe_finRotate_of_ne_last last]
      have different_a : i.val ≠ a.val := fun equal => not_a (Fin.ext equal)
      have different_b : i.val ≠ finish.val - 1 := fun equal => not_b (Fin.ext equal)
      omega

end Unfoldings
