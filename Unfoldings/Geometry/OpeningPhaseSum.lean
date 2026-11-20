module

public import Unfoldings.Cone.Sector
public import Unfoldings.Topology.FiniteCyclicTurns

/-! Real opening increments add before taking the phase of the final bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped BigOperators

/-- The accumulated real heading lifts the ratio of the first and last
circle directions. No common principal-argument branch is required. -/
theorem circle_exp_sum_eq_final_ratio {n : ℕ} (direction : Fin (n + 1) → Circle)
    (turn : Fin n → ℝ)
    (step : ∀ i, Circle.exp (turn i) = direction i.succ / direction i.castSucc) :
    Circle.exp (∑ i, turn i) = direction (Fin.last n) / direction 0 := by
  have accumulated (i : Fin (n + 1)) :
      Circle.exp (Fin.partialSum turn i) * direction 0 = direction i := by
    refine Fin.induction ?_ (fun k previous => ?_) i
    · rw [Fin.partialSum_zero, Circle.exp_zero, one_mul]
    · rw [Fin.partialSum_succ, add_comm, Circle.exp_add, mul_assoc, previous, step,
        div_mul_cancel]
  have full : Fin.partialSum turn (Fin.last n) = ∑ i, turn i := by
    change ((List.ofFn turn).take n).sum = _
    rw [List.take_of_length_le (by simp), List.sum_ofFn]
  have identity := accumulated (Fin.last n)
  rw [full] at identity
  exact eq_div_iff_mul_eq'.mpr identity

/-- Positive opening at one step and nonnegative openings elsewhere give a
strictly positive final relative phase as long as their sum is below `π`. -/
theorem circle_final_ratio_im_pos_of_sum {n : ℕ} (direction : Fin (n + 1) → Circle)
    (turn : Fin n → ℝ)
    (step : ∀ i, Circle.exp (turn i) = direction i.succ / direction i.castSucc)
    (nonnegative : ∀ i, 0 ≤ turn i) (strict : ∃ i, 0 < turn i)
    (small : (∑ i, turn i) < Real.pi) :
    0 < ((direction (Fin.last n) / direction 0 : Circle) : ℂ).im := by
  have positive : 0 < ∑ i, turn i := by
    obtain ⟨i, hi⟩ := strict
    exact Finset.sum_pos' (fun j _ => nonnegative j) ⟨i, Finset.mem_univ _, hi⟩
  rw [← circle_exp_sum_eq_final_ratio direction turn step]
  change 0 < (polarRay (∑ i, turn i)).im
  rw [polarRay_im]
  exact Real.sin_pos_of_pos_of_lt_pi positive small

end Unfoldings
