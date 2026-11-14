module

public import Mathlib.Algebra.BigOperators.Fin

/-! Exact sums of a prescribed prefix of a longer finite sequence. -/

@[expose] public section

namespace Unfoldings

theorem fin_partialSum_prefix {M : Type*} [AddCommMonoid M] {n m : ℕ} (longer : n ≤ m)
    (f : Fin m → M) (g : Fin n → M) (same : ∀ i, f (i.castLE longer) = g i) :
    Fin.partialSum f ⟨n, by omega⟩ = ∑ i, g i := by
  classical
  cases n with
  | zero => simp [Fin.partialSum]
  | succ n =>
    have cutoff : Finset.univ.filter (fun i : Fin m => i.val < n + 1) =
        Finset.Iic ((Fin.last n).castLE longer) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      change i.val < n + 1 ↔ i.val ≤ n
      omega
    rw [Fin.partialSum, List.sum_take_ofFn, cutoff, Fin.sum_Iic_castLE longer f (Fin.last n)]
    have full : Finset.Iic (Fin.last n) = Finset.univ := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last i
    rw [full]
    exact Finset.sum_congr rfl (fun i _ => same i)

end Unfoldings
