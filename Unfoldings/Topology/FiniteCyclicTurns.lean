module

public import Unfoldings.Topology.CyclicRegionTurns
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! An exact real heading prefix equals a region's turns when its entering bank starts the cycle. -/

@[expose] public section

namespace Unfoldings

variable {A : Type*} [AddCommGroup A] {n : ℕ}

open Classical in
/-- The cycle's closing turn is irrelevant when the selected region omits its starting vertex. -/
theorem partialSum_turns_eq_region_sum (turn : Fin (n + 1) → A)
    (inside : Fin (n + 1) → Prop) (leave : Fin (n + 1))
    (enters : ¬ inside 0 ∧ inside (finRotate (n + 1) 0))
    (leaves : inside leave ∧ ¬ inside (finRotate (n + 1) leave))
    (stable : ∀ i, i ≠ 0 → i ≠ leave →
      (inside (finRotate (n + 1) i) ↔ inside i)) :
    Fin.partialSum (fun i : Fin n => turn i.succ) leave =
      ∑ i, if inside i then turn i else 0 := by
  let heading := Fin.partialSum (fun i : Fin n => turn i.succ)
  have step (i : Fin (n + 1)) (selected : inside (finRotate (n + 1) i)) :
      heading (finRotate (n + 1) i) - heading i = turn (finRotate (n + 1) i) := by
    revert selected
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [finRotate_last]
      exact fun contradiction => (enters.1 contradiction).elim
    · rw [show finRotate (n + 1) k.castSucc = k.succ from finRotate_of_lt k.isLt]
      intro _
      change Fin.partialSum _ k.succ - Fin.partialSum _ k.castSucc = _
      rw [Fin.partialSum_succ]
      exact add_sub_cancel_left _ _
  have different : (0 : Fin (n + 1)) ≠ leave := by
    intro equal
    exact enters.1 (equal.symm ▸ leaves.1)
  have sum := sum_turn_of_two_region_exits (finRotate (n + 1)) inside heading turn step 0 leave
    different enters leaves stable
  simpa only [heading, Fin.partialSum_zero, sub_zero] using sum.symm

end Unfoldings
