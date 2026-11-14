module

public import Unfoldings.Geometry.PlanarAngleArea

/-! Sine distortion under a planar linear equivalence with controlled length contraction. -/

@[expose] public section

namespace Unfoldings

/-- Length contraction between c and one bounds the actual area contraction between c² and one. -/
theorem orientationScale_bounds_of_norm_bounds (A : Plane ≃ₗ[ℝ] Plane) {c : ℝ}
    (positive : 0 < c) (lower : ∀ x, c * ‖x‖ ≤ ‖A x‖) (upper : ∀ x, ‖A x‖ ≤ ‖x‖) :
    c ^ 2 ≤ |orientationScale A.toLinearMap.toAffineMap| ∧
      |orientationScale A.toLinearMap.toAffineMap| ≤ 1 := by
  let e₀ : Plane := EuclideanSpace.single 0 1
  let e₁ : Plane := EuclideanSpace.single 1 1
  have norm₀ : ‖e₀‖ = 1 := by simp [e₀, EuclideanSpace.single]
  have norm₁ : ‖e₁‖ = 1 := by simp [e₁, EuclideanSpace.single]
  let s := |orientationScale A.toLinearMap.toAffineMap|
  have s_nonnegative : 0 ≤ s := abs_nonneg _
  have s_upper : s ≤ 1 := by
    have area := abs_orient_le_norm_mul (A e₀) (A e₁)
    have first := upper e₀
    have last := upper e₁
    rw [norm₀] at first
    rw [norm₁] at last
    exact area.trans ((mul_le_mul first last (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))
  have first : c * ‖A.symm e₀‖ ≤ 1 := by
    simpa only [A.apply_symm_apply, norm₀] using lower (A.symm e₀)
  have last : c * ‖A.symm e₁‖ ≤ 1 := by
    simpa only [A.apply_symm_apply, norm₁] using lower (A.symm e₁)
  have product : c ^ 2 * (‖A.symm e₀‖ * ‖A.symm e₁‖) ≤ 1 := by
    have bound := (mul_le_mul first last
      (mul_nonneg positive.le (norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)
    nlinarith [bound]
  have area := mul_le_mul_of_nonneg_left (abs_orient_le_norm_mul (A.symm e₀) (A.symm e₁))
    (sq_nonneg c)
  have area_bound : c ^ 2 * |orient 0 (A.symm e₀) (A.symm e₁)| ≤ 1 := area.trans product
  have scale := congrArg abs
    (orient_affine_linear A.toLinearMap.toAffineMap (A.symm e₀) (A.symm e₁))
  have inverse : 1 = s * |orient 0 (A.symm e₀) (A.symm e₁)| := by
    simpa [s, e₀, e₁, orient, EuclideanSpace.single, abs_mul] using scale
  refine ⟨?_, s_upper⟩
  calc
    c ^ 2 = s * (c ^ 2 * |orient 0 (A.symm e₀) (A.symm e₁)|) := by
      rw [mul_left_comm, ← inverse, mul_one]
    _ ≤ s * 1 := mul_le_mul_of_nonneg_left area_bound s_nonnegative
    _ = s := mul_one s

/-- The angular sine ratio is close to one even for arbitrarily small actual corner angles. -/
theorem angle_sine_bounds_of_norm_bounds (A : Plane ≃ₗ[ℝ] Plane) {c : ℝ}
    (positive : 0 < c) (lower : ∀ x, c * ‖x‖ ≤ ‖A x‖) (upper : ∀ x, ‖A x‖ ≤ ‖x‖)
    {x y : Plane} (xne : x ≠ 0) (yne : y ≠ 0) :
    c ^ 2 * Real.sin (InnerProductGeometry.angle x y) ≤
        Real.sin (InnerProductGeometry.angle (A x) (A y)) ∧
      c ^ 2 * Real.sin (InnerProductGeometry.angle (A x) (A y)) ≤
        Real.sin (InnerProductGeometry.angle x y) := by
  obtain ⟨scale_lower, scale_upper⟩ := orientationScale_bounds_of_norm_bounds A positive lower upper
  let s := |orientationScale A.toLinearMap.toAffineMap|
  let a := Real.sin (InnerProductGeometry.angle x y)
  let b := Real.sin (InnerProductGeometry.angle (A x) (A y))
  let p := ‖x‖ * ‖y‖
  let q := ‖A x‖ * ‖A y‖
  have pp : 0 < p := mul_pos (norm_pos_iff.mpr xne) (norm_pos_iff.mpr yne)
  have ap : 0 ≤ a := InnerProductGeometry.sin_angle_nonneg _ _
  have bp : 0 ≤ b := InnerProductGeometry.sin_angle_nonneg _ _
  have q_upper : q ≤ p := mul_le_mul (upper x) (upper y) (norm_nonneg _) (norm_nonneg _)
  have q_lower : c ^ 2 * p ≤ q := by
    have bound := mul_le_mul (lower x) (lower y)
      (mul_nonneg positive.le (norm_nonneg _)) (norm_nonneg _)
    nlinarith [bound]
  have area := congrArg abs (orient_affine_linear A.toLinearMap.toAffineMap x y)
  rw [abs_mul, abs_orient_eq_sin_angle_mul_norm, abs_orient_eq_sin_angle_mul_norm] at area
  change b * q = s * (a * p) at area
  constructor
  · apply (mul_le_mul_iff_of_pos_right pp).mp
    calc
      c ^ 2 * a * p ≤ s * (a * p) := by
        nlinarith [mul_le_mul_of_nonneg_right scale_lower (mul_nonneg ap pp.le)]
      _ = b * q := area.symm
      _ ≤ b * p := mul_le_mul_of_nonneg_left q_upper bp
  · apply (mul_le_mul_iff_of_pos_right pp).mp
    calc
      c ^ 2 * b * p ≤ b * q := by
        nlinarith [mul_le_mul_of_nonneg_left q_lower bp]
      _ = s * (a * p) := area
      _ ≤ a * p := mul_le_of_le_one_left (mul_nonneg ap pp.le) scale_upper

end Unfoldings
