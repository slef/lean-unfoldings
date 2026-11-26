module

public import Unfoldings.Geometry.MinorArcArclength
public import Unfoldings.Cap.Gnomonic

/-! Exact chord and tangent determinant identities for spherical triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

/-- The signed determinant of three spatial rays in their given order. -/
def spatialRayDet (u v w : Space) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) +
    u 2 * (v 0 * w 1 - v 1 * w 0)

theorem spatialRayDet_sq_eq_gram (u v w : Space) :
    spatialRayDet u v w ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2 +
      2 * inner ℝ u v * inner ℝ u w * inner ℝ v w -
      ‖u‖ ^ 2 * inner ℝ v w ^ 2 - ‖v‖ ^ 2 * inner ℝ u w ^ 2 -
      ‖w‖ ^ 2 * inner ℝ u v ^ 2 := by
  simp only [spatialRayDet, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three,
    Real.inner_apply]
  ring

/-- The squared sine of a spherical side is a polynomial in its squared chord. -/
theorem sphericalSide_sin_sq_eq_chord (u v : Space) (unit_u : ‖u‖ = 1) (unit_v : ‖v‖ = 1) :
    sin (angle u v) ^ 2 = ‖u - v‖ ^ 2 * (1 - ‖u - v‖ ^ 2 / 4) := by
  have chord : ‖u - v‖ ^ 2 = 2 - 2 * cos (angle u v) := by
    rw [norm_sub_pow_two_real, unit_u, unit_v, inner_eq_cos_angle_of_norm_eq_one unit_u unit_v]
    ring
  rw [chord]
  linear_combination sin_sq_add_cos_sq (angle u v)

private theorem tangentVector_inner (u v w : Space) (unit : ‖u‖ = 1) :
    inner ℝ (v - inner ℝ u v • u) (w - inner ℝ u w • u) =
      inner ℝ v w - inner ℝ u v * inner ℝ u w := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unit, one_pow]
  rw [real_inner_comm v u]
  ring

/-- A spherical corner's sine times the sines of its incident sides is the
unsigned determinant of the three actual unit vertices. -/
theorem sphericalCorner_sin_mul_sides (u v w : Space) (unit_u : ‖u‖ = 1)
    (unit_v : ‖v‖ = 1) (unit_w : ‖w‖ = 1)
    (sv : 0 < sin (angle u v)) (sw : 0 < sin (angle u w)) :
    sin (angle (minorArcTangent u v) (minorArcTangent u w)) *
      (sin (angle u v) * sin (angle u w)) = |spatialRayDet u v w| := by
  let x := v - inner ℝ u v • u
  let y := w - inner ℝ u w • u
  have cosv := inner_eq_cos_angle_of_norm_eq_one unit_u unit_v
  have cosw := inner_eq_cos_angle_of_norm_eq_one unit_u unit_w
  have norm_x : ‖x‖ ^ 2 = sin (angle u v) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (v - inner ℝ u v • u) (v - inner ℝ u v • u) = _
    rw [tangentVector_inner u v v unit_u, real_inner_self_eq_norm_sq, unit_v, one_pow, cosv]
    nlinarith only [sin_sq_add_cos_sq (angle u v)]
  have norm_y : ‖y‖ ^ 2 = sin (angle u w) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (w - inner ℝ u w • u) (w - inner ℝ u w • u) = _
    rw [tangentVector_inner u w w unit_u, real_inner_self_eq_norm_sq, unit_w, one_pow, cosw]
    nlinarith only [sin_sq_add_cos_sq (angle u w)]
  have vx : ‖x‖ = sin (angle u v) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, abs_of_pos sv] using congrArg Real.sqrt norm_x
  have wy : ‖y‖ = sin (angle u w) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, abs_of_pos sw] using congrArg Real.sqrt norm_y
  have v_tangent : minorArcTangent u v = (sin (angle u v))⁻¹ • x := by
    rw [minorArcTangent, ← cosv]
  have w_tangent : minorArcTangent u w = (sin (angle u w))⁻¹ • y := by
    rw [minorArcTangent, ← cosw]
  have gram : ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 = spatialRayDet u v w ^ 2 := by
    have xx : ‖x‖ ^ 2 = 1 - inner ℝ u v * inner ℝ u v := by
      rw [← real_inner_self_eq_norm_sq]
      exact (tangentVector_inner u v v unit_u).trans (by rw [real_inner_self_eq_norm_sq, unit_v, one_pow])
    have yy : ‖y‖ ^ 2 = 1 - inner ℝ u w * inner ℝ u w := by
      rw [← real_inner_self_eq_norm_sq]
      exact (tangentVector_inner u w w unit_u).trans (by rw [real_inner_self_eq_norm_sq, unit_w, one_pow])
    have xy : inner ℝ x y = _ := tangentVector_inner u v w unit_u
    rw [xx, yy, xy, spatialRayDet_sq_eq_gram, unit_u, unit_v, unit_w, one_pow]
    ring
  rw [v_tangent, w_tangent, angle_smul_left_of_pos _ _ (inv_pos.mpr sv),
    angle_smul_right_of_pos _ _ (inv_pos.mpr sw), ← vx, ← wy, sin_angle_mul_norm_mul_norm,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← pow_two, gram, Real.sqrt_sq_eq_abs]

end Unfoldings
