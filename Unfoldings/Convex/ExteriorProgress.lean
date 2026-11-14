module

public import Unfoldings.Convex.ExteriorPlan
public import Unfoldings.Convex.AnnularProgress

/-! Safe exterior rays have the same quantitative common-potential progress as interior paths. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V)

theorem slope_mem_frontier (v : V) : R.slope v ∈ frontier E.slopes := by
  refine ⟨subset_closure (R.active v).1, ?_⟩
  intro inside
  have nonzero : R.direction (R.slope v) ≠ 0 := by
    intro zero
    have unit := R.unit v
    rw [zero, norm_zero] at unit
    norm_num at unit
  exact (lt_irrefl _ ((E.interior_slope_lt nonzero (R.support v) inside)))

theorem boundary_height_ray (boundary : (frontier E.slopes).Nonempty) (v : V) {t : ℝ}
    (time : 0 ≤ t) :
    (E.boundaryEnvelope boundary).height (R.ray v t) = E.height (R.ray v t) :=
  E.boundary_height_ray (R.active v) (R.slope_mem_frontier v) rfl (R.support v) time

theorem rate_ge {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) (v : V) : a ≤ R.rate v := by
  have closed_disk : Metric.closedBall (0 : Plane) a ⊆ E.slopes := by
    rw [← closure_ball (0 : Plane) positive.ne']
    exact closure_minimal inner_disk E.compact.isClosed
  have point : a • R.direction (R.slope v) ∈ E.slopes := by
    apply closed_disk
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, R.unit,
      Real.norm_of_nonneg positive.le, mul_one]
  have bound := R.support v _ point
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, R.unit, one_pow, mul_one] at bound
  exact bound

/-- Each finite contact edge gains at least a per unit projected length in the common
boundary potential. Rays may meet and follow an optional flat root's assigned continuation. -/
theorem contact_boundary_progress {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
    (boundary : (frontier E.slopes).Nonempty) {v w : V} (contact : R.Contact v w) :
    a * ‖R.point w - R.point v‖ ≤
      (E.boundaryEnvelope boundary).height (R.point w) -
        (E.boundaryEnvelope boundary).height (R.point v) := by
  obtain ⟨t, tpos, equal⟩ := contact
  have start := R.boundary_height_ray boundary v (t := 0) le_rfl
  simp only [ray, zero_smul, add_zero] at start
  rw [equal, R.boundary_height_ray boundary v tpos.le, start, R.height_ray v tpos.le]
  have displacement : R.ray v t - R.point v = t • R.direction (R.slope v) := by
    dsimp [ray]
    abel
  rw [displacement, norm_smul, R.unit, Real.norm_of_nonneg tpos.le, mul_one]
  have lower := R.rate_ge positive inner_disk v
  nlinarith

end Unfoldings.SlopeEnvelope.ExteriorPlan
