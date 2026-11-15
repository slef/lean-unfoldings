module

public import Unfoldings.Convex.ExteriorPlan
public import Unfoldings.Convex.FiniteSlopeModel
public import Mathlib.Topology.MetricSpace.Dilation

/-! Exact spatial affine geometry and speed of the actual whole exterior rays. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V) (M : E.FiniteSlopeModel)

/-- The full spatial velocity includes the actual descending roof height. -/
def spatialDirection (v : V) : Space :=
  Cap.horizontalAtHeight (R.direction (R.slope v)) (-R.rate v)

theorem spatialDirection_ne_zero (v : V) : R.spatialDirection v ≠ 0 := by
  intro zero
  have horizontal := congrArg Cap.horizontal zero
  simp only [spatialDirection, Cap.horizontal_horizontalAtHeight, map_zero] at horizontal
  have unit := R.unit v
  rw [horizontal, norm_zero] at unit
  norm_num at unit

/-- The speed is intrinsic spatial speed, with the vertical component retained. -/
theorem spatialDirection_norm_sq (v : V) :
    ‖R.spatialDirection v‖ ^ 2 = 1 + R.rate v ^ 2 := by
  rw [Cap.horizontal_norm_sq, spatialDirection, Cap.horizontal_horizontalAtHeight,
    Cap.height_horizontalAtHeight, R.unit]
  ring

/-- An actual exterior ray lifts to one straight spatial ray on its whole positive domain. -/
theorem spatial_point_ray (v : V) {t : ℝ} (time : 0 ≤ t) :
    SpatialEnvelope.point M.plane (R.ray v t) =
      SpatialEnvelope.point M.plane (R.point v) + t • R.spatialDirection v := by
  ext j
  fin_cases j
  · simp [SpatialEnvelope.point, ray, spatialDirection, Cap.horizontalAtHeight,
      PiLp.add_apply, PiLp.smul_apply]
  · simp [SpatialEnvelope.point, ray, spatialDirection, Cap.horizontalAtHeight,
      PiLp.add_apply, PiLp.smul_apply]
  · change SpatialEnvelope.point M.plane (R.ray v t) 2 =
      (SpatialEnvelope.point M.plane (R.point v) + t • R.spatialDirection v) 2
    rw [SpatialEnvelope.height_point, PiLp.add_apply, PiLp.smul_apply,
      SpatialEnvelope.height_point, spatialDirection, Cap.height_horizontalAtHeight,
      M.height_eq, M.height_eq, R.height_ray v time]
    ring

/-- Exact differences of arbitrary positive ray points, including the full height difference. -/
theorem spatial_ray_sub (v : V) {s t : ℝ} (first : 0 ≤ s) (last : 0 ≤ t) :
    SpatialEnvelope.point M.plane (R.ray v s) - SpatialEnvelope.point M.plane (R.ray v t) =
      (s - t) • R.spatialDirection v := by
  rw [R.spatial_point_ray M v first, R.spatial_point_ray M v last,
    add_sub_add_left_eq_sub, sub_smul]

theorem edist_spatial_ray (v : V) {s t : ℝ} (first : 0 ≤ s) (last : 0 ≤ t) :
    edist (SpatialEnvelope.point M.plane (R.ray v s))
      (SpatialEnvelope.point M.plane (R.ray v t)) =
        (‖R.spatialDirection v‖₊ : ℝ≥0∞) * edist s t := by
  rw [edist_dist, dist_eq_norm, R.spatial_ray_sub M v first last,
    norm_smul, Real.norm_eq_abs, edist_dist, Real.dist_eq,
    ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]

/-- The entire spatial tail is a dilation, with no upper endpoint or asymptotic error. -/
def spatialRayTailDilation (v : V) (T : ℝ) (nonnegative : 0 ≤ T) : Set.Ici T →ᵈ Space where
  toFun t := SpatialEnvelope.point M.plane (R.ray v t.val)
  edist_eq' := ⟨‖R.spatialDirection v‖₊, nnnorm_ne_zero_iff.mpr (R.spatialDirection_ne_zero v),
    fun s t => R.edist_spatial_ray M v (nonnegative.trans s.property)
      (nonnegative.trans t.property)⟩

end Unfoldings.SlopeEnvelope.ExteriorPlan
