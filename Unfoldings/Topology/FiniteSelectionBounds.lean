module

public import Unfoldings.Topology.FiniteMonotoneSelection

/-! A common two-sided increment bound survives arbitrary continuous finite branch changes. -/

@[expose] public section

namespace Unfoldings

theorem finite_selection_abs_bound {ι : Type*} [Finite ι]
    (input selected : unitInterval → ℝ) (input_continuous : Continuous input)
    (selected_continuous : Continuous selected) (c : ℝ)
    (branch : ι → unitInterval → ℝ) (branch_continuous : ∀ i, Continuous (branch i))
    (bound : ∀ i a b, a ≤ b → |branch i b - branch i a| ≤ c * (input b - input a))
    (selection : ∀ t, ∃ i, selected t = branch i t) :
    |selected 1 - selected 0| ≤ c * (input 1 - input 0) := by
  have lower := finite_monotone_selection_endpoints
    (fun i t => branch i t + c * input t)
    (fun i => (branch_continuous i).add (continuous_const.mul input_continuous))
    (fun i a b ordered => by
      have estimate := (abs_le.mp (bound i a b ordered)).1
      dsimp only
      linarith)
    (fun t => selected t + c * input t)
    (selected_continuous.add (continuous_const.mul input_continuous))
    (fun t => (selection t).imp (fun _ same => congrArg (fun r => r + c * input t) same))
  have upper := finite_monotone_selection_endpoints
    (fun i t => c * input t - branch i t)
    (fun i => (continuous_const.mul input_continuous).sub (branch_continuous i))
    (fun i a b ordered => by
      have estimate := (abs_le.mp (bound i a b ordered)).2
      dsimp only
      linarith)
    (fun t => c * input t - selected t)
    ((continuous_const.mul input_continuous).sub selected_continuous)
    (fun t => (selection t).imp (fun _ same => congrArg (fun r => c * input t - r) same))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Unfoldings
