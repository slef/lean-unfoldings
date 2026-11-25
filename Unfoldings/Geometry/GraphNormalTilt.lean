module

public import Unfoldings.Geometry.SpatialPlaneSlopes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith

/-! A slope chart radius gives the vertical height of the unit graph normal. -/

@[expose] public section

namespace Unfoldings.SpatialPlane

open Real

/-- The slope radius controls the vertical component of the actual unit normal. -/
theorem ofGraph_normal_height_of_slope_radius {φ : ℝ} (pos : 0 < φ) (small : φ < π / 2)
    (h : ℝ) (s : Plane) (radius : ‖s‖ ≤ tan φ) : cos φ ≤ (ofGraph h s).normal 2 := by
  have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [pos, pi_pos], small⟩
  have sq := pow_le_pow_left₀ (norm_nonneg _) radius 2
  have tc : tan φ * cos φ = sin φ := by
    rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ cp.ne']
  have exact_sq : tan φ ^ 2 * cos φ ^ 2 = sin φ ^ 2 := by
    rw [← mul_pow, tc]
  apply graphNormal_vertical_ge cp.le
  have product := mul_le_mul_of_nonneg_right sq (sq_nonneg (cos φ))
  nlinarith only [product, exact_sq, sin_sq_add_cos_sq φ]

end Unfoldings.SpatialPlane
