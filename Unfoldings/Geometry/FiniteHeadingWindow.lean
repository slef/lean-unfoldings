module

public import Unfoldings.Geometry.ChainConstruction

/-! The heading of the last link sums exactly the strict internal vertex turns. -/

@[expose] public section

namespace Unfoldings

/-- Omitting both endpoint turns leaves the genuine heading prefix of the last bank. -/
theorem partialSum_succ_eq_strict_window {A : Type*} [AddCommMonoid A] {n : ℕ}
    (weight : Fin (n + 1) → A) (cut : Fin (n + 1)) :
    Fin.partialSum (fun k : Fin n => weight k.succ)
      (⟨cut.val - 1, by omega⟩ : Fin (n + 1)) =
        ∑ j : Fin (n + 1), if 0 < j ∧ j < cut then weight j else 0 := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [lt_self_iff_false, false_and, ite_false, zero_add]
  simp only [Fin.partialSum, List.sum_take_ofFn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  have equivalent : k.val < cut.val - 1 ↔ (0 : Fin (n + 1)) < k.succ ∧ k.succ < cut := by
    change k.val < cut.val - 1 ↔ 0 < k.val + 1 ∧ k.val + 1 < cut.val
    omega
  simp only [equivalent]

end Unfoldings
