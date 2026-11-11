module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Order.Fin.Basic

/-! Ordered finite monotone pieces remain ordered across jumps with the same sign. -/

@[expose] public section

namespace Unfoldings

theorem finite_monotone_pieces {α : Type*} [Preorder α] {n : ℕ}
    (F : Fin n → unitInterval → α) (within : ∀ i, Monotone (F i))
    (jump : ∀ i j : Fin n, j.val = i.val + 1 → F i 1 ≤ F j 0)
    (i j : Fin n) (s t : unitInterval)
    (before : i < j ∨ i = j ∧ s ≤ t) : F i s ≤ F j t := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have starts : Monotone (fun k : Fin (n + 1) => F k 0) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro k
      exact (within k.castSucc zero_le_one).trans (jump k.castSucc k.succ rfl)
    rcases before with before | ⟨rfl, ordered⟩
    · let next : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      exact (within i (show s ≤ 1 from s.property.2)).trans
        ((jump i next rfl).trans ((starts (show next ≤ j by change i.val + 1 ≤ j.val; omega)).trans
          (within j (show 0 ≤ t from t.property.1))))
    · exact within _ ordered

end Unfoldings
