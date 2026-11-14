module

public import Unfoldings.Geometry.AffineOrientation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Exact unsigned angular area and area bounds for actual planar linear maps. -/

@[expose] public section

namespace Unfoldings

/-- The planar Gram determinant is the square of the actual signed area. -/
theorem orient_sq_eq_gram (x y : Plane) :
    orient 0 x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ x y) ^ 2 := by
  simp only [orient, PiLp.zero_apply, sub_zero, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  ring

/-- Unsigned angular area, including zero and collinear vectors. -/
theorem abs_orient_eq_sin_angle_mul_norm (x y : Plane) :
    |orient 0 x y| = Real.sin (InnerProductGeometry.angle x y) * (‖x‖ * ‖y‖) := by
  rw [InnerProductGeometry.sin_angle_mul_norm_mul_norm, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, ← pow_two, ← orient_sq_eq_gram,
    Real.sqrt_sq_eq_abs]

/-- Signed area never exceeds the product of the actual vector lengths. -/
theorem abs_orient_le_norm_mul (x y : Plane) : |orient 0 x y| ≤ ‖x‖ * ‖y‖ := by
  rw [abs_orient_eq_sin_angle_mul_norm]
  exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Real.sin_le_one _)

end Unfoldings
