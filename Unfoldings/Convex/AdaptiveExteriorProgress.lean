module

public import Unfoldings.Convex.ExteriorProgress
public import Unfoldings.Convex.HistoryCone

/-! Adaptive history progress and radial bounds on assigned exterior rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V)
  (boundary : (frontier E.slopes).Nonempty) {L : Set Plane}

/-- The supporting outward direction of a root belongs to its history cone
when the progress body lies in the clipped slope domain. -/
theorem direction_mem_historyCone (within : L ⊆ E.slopes) (v : V) :
    R.direction (R.slope v) ∈ historyCone L (R.slope v) := by
  intro w hw
  simpa only [real_inner_comm w (R.direction _), real_inner_comm (R.slope v) (R.direction _)] using
    R.support v w (within hw)

theorem active_boundary_at_point (v : V) :
    (E.boundaryEnvelope boundary).Active (R.point v) (R.slope v) :=
  E.active_boundary boundary (R.active v) (R.slope_mem_frontier v)

/-- Every exterior subsegment preserves the same invariant as the interior edges. -/
theorem historyProgress_ray (within : L ⊆ E.slopes) (v : V) {s t : ℝ}
    (start : 0 ≤ s) (ordered : s ≤ t) :
    (E.boundaryEnvelope boundary).HistoryProgress L (R.ray v s) (R.ray v t) :=
  (E.boundaryEnvelope boundary).historyProgress_ray (R.active_boundary_at_point boundary v)
    (R.direction_mem_historyCone within v) start ordered

/-- A certified positive polar margin at the root persists along the entire ray,
uniformly for every history reaching the root. -/
theorem radial_margin_ray (v : V) {η : ℝ} (nonnegative : 0 ≤ η) (small : η ≤ 1)
    (polar : ∀ z ∈ historyCone L (R.slope v),
      η * ‖z‖ ≤ inner ℝ z (R.direction (R.slope v)))
    {q : Plane} (history : (E.boundaryEnvelope boundary).HistoryProgress L q (R.point v))
    {t : ℝ} (time : 0 ≤ t) :
    η * ‖R.ray v t - q‖ ≤ inner ℝ (R.ray v t - q) (R.direction (R.slope v)) := by
  have incoming := history.mem_historyCone (E.boundaryEnvelope boundary)
    (R.active_boundary_at_point boundary v)
  have margin : η * (‖R.point v - q‖ * ‖R.direction (R.slope v)‖) ≤
      inner ℝ (R.point v - q) (R.direction (R.slope v)) := by
    rw [R.unit, mul_one]
    exact polar _ incoming
  have later := inner_radial_margin_add_smul (R.point v - q) (R.direction (R.slope v))
    nonnegative small time margin
  rw [R.unit, mul_one, show R.point v - q + t • R.direction (R.slope v) = R.ray v t - q by
    dsimp [ray]; abel] at later
  exact later

end Unfoldings.SlopeEnvelope.ExteriorPlan
