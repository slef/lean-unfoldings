module

public import Mathlib.Order.Fin.Basic

/-! Two marked vertices split a finite cyclic bank order into two constant runs. -/

@[expose] public section

namespace Unfoldings

/-- Equality of consecutive values propagates along a genuine finite interval. -/
theorem fin_eq_of_steps_on_interval {A : Sort*} {n : ℕ} (label : Fin (n + 1) → A)
    {a b : Fin (n + 1)} (ordered : a ≤ b)
    (step : ∀ i : Fin n, a ≤ i.castSucc → i.succ ≤ b → label i.succ = label i.castSucc) :
    label b = label a := by
  have walk (b : Fin (n + 1)) : ∀ a ≤ b,
      (∀ i : Fin n, a ≤ i.castSucc → i.succ ≤ b → label i.succ = label i.castSucc) →
        label b = label a := by
    refine Fin.induction ?_ (fun k previous => ?_) b
    · intro a before _
      have equal : a = 0 := le_antisymm before (Fin.zero_le _)
      rw [equal]
    · intro a before steps
      by_cases same : a = k.succ
      · rw [same]
      · have earlier : a ≤ k.castSucc := by
          have bound : a.val ≤ k.val + 1 := before
          have different : a.val ≠ k.val + 1 := fun equal => same (Fin.ext equal)
          change a.val ≤ k.val
          omega
        have kept := previous a earlier (fun i first last =>
          steps i first (last.trans (by change k.val ≤ k.val + 1; omega)))
        exact (steps k earlier le_rfl).trans kept
  exact walk b a ordered step

/-- With one interior transition allowed, the two runs are determined by their first labels. -/
theorem fin_two_runs_of_steps {A : Sort*} {n : ℕ} (label : Fin (n + 1) → A)
    (cut : Fin (n + 1))
    (step : ∀ i : Fin n, i.succ ≠ cut → label i.succ = label i.castSucc)
    (i : Fin (n + 1)) : label i = if i < cut then label 0 else label cut := by
  classical
  by_cases before : i < cut
  · rw [ite_eq_left before]
    apply fin_eq_of_steps_on_interval label (Fin.zero_le _)
    intro j _ last
    exact step j (ne_of_lt (last.trans_lt before))
  · rw [ite_eq_right before]
    apply fin_eq_of_steps_on_interval label (le_of_not_gt before)
    intro j first _
    apply step j
    apply ne_of_gt
    exact first.trans_lt (by change j.val < j.val + 1; omega)

end Unfoldings
