module

public import Unfoldings.Cap.RadialStripPointOrder
public import Unfoldings.Cap.StripCircleBanks
public import Unfoldings.Geometry.WeakCircleCaps

/-! A controlling circle coordinate identifies the actual physical strip-bank point. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  {μ : ℝ} (small_error : ε < μ)
  (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius)

include small_error margin radius_positive

theorem closed_circle_point_eq_upper_of_horizontal_eq {z : ℂ}
    (closed : z ∈ closure data.strictDomain)
    (size : ‖data.value z - data.center‖ = radius)
    (horizontal : (data.value z - data.center).re =
      (data.value (S.upper.point slice.upperHeight) - data.center).re) :
    z = S.upper.point slice.upperHeight := by
  have height := data.closed_height_pos_of_norm closed (by rw [size]; exact radius_positive)
  have upper_height := data.closed_height_pos_of_norm slice.upper_closed
    (by rw [slice.upper_radius]; exact radius_positive)
  have quadrant := data.strict_quadrant_of_closed_margin small_error margin closed height
  have upper_quadrant := data.strict_quadrant_of_closed_margin small_error margin
    slice.upper_closed upper_height
  have equal := complex_eq_of_norm_re_eq (size.trans slice.upper_radius.symm) horizontal
    quadrant.2.le upper_quadrant.2.le
  have values : data.value z = data.value (S.upper.point slice.upperHeight) :=
    sub_left_inj.mp equal
  exact data.closed_injective closed slice.upper_closed values

theorem closed_circle_point_eq_lower_of_vertical_eq {z : ℂ}
    (closed : z ∈ closure data.strictDomain)
    (size : ‖data.value z - data.center‖ = radius)
    (vertical : (data.value z - data.center).im =
      (data.value (S.lower.point slice.lowerHeight) - data.center).im) :
    z = S.lower.point slice.lowerHeight := by
  have height := data.closed_height_pos_of_norm closed (by rw [size]; exact radius_positive)
  have lower_height := data.closed_height_pos_of_norm slice.lower_closed
    (by rw [slice.lower_radius]; exact radius_positive)
  have quadrant := data.strict_quadrant_of_closed_margin small_error margin closed height
  have lower_quadrant := data.strict_quadrant_of_closed_margin small_error margin
    slice.lower_closed lower_height
  have equal := complex_eq_of_norm_im_eq (size.trans slice.lower_radius.symm) vertical
    quadrant.1.le lower_quadrant.1.le
  have values : data.value z = data.value (S.lower.point slice.lowerHeight) :=
    sub_left_inj.mp equal
  exact data.closed_injective closed slice.lower_closed values

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
