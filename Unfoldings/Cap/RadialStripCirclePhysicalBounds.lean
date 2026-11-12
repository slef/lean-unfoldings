module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Geometry.MonotoneStripSourceError

/-! Actual approached source-circle points stay in a quantitative physical source ball. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

theorem closed_circle_point_mem_ball
    (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
    (small_error : ε < 1 / 2) {z : ℂ} (closed : z ∈ closure data.strictDomain)
    {radius bound : ℝ} (size : ‖data.value z - data.center‖ = radius)
    (far : radius < (1 / 2 - ε) * bound) :
    source + (fiveSectorFrame t positive small i).place.symm z ∈ Metric.ball source bound := by
  have bounded := data.closed_bounded closed
  have coordinates := S.carrier_coordinates_nonnegative data.lower_source data.upper_source
    bounded.1 bounded.2.1
  have norm_bound : ‖z‖ ≤ z.re + z.im := by
    simpa only [abs_of_nonneg coordinates.1, abs_of_nonneg coordinates.2] using
      Complex.norm_le_abs_re_add_abs_im z
  have lower := data.closed_distance_lower closed
  rw [size] at lower
  have coefficient : 0 < 1 / 2 - ε := sub_pos.mpr small_error
  have height : z.re + z.im < bound := by nlinarith
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
  exact norm_bound.trans_lt height

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
