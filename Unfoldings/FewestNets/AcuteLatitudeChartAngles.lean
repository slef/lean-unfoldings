module

public import Unfoldings.FewestNets.AcuteLatitudeOrientedChart
public import Unfoldings.Geometry.SlopeAngles
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The exact altitude and side ratios of the annular charts control their three corner angles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real InnerProductGeometry

/-- Arctangent changes by at least 0.897 times the slope difference
throughout the long-side range of the revised annular charts. -/
theorem arctan_spread_lower {u v : ℝ} (ordered : u < v)
    (u_bound : |u| ≤ 0.338) (v_bound : |v| ≤ 0.338) :
    0.897 * (v - u) < arctan v - arctan u := by
  obtain ⟨c, between, derivative⟩ := exists_deriv_eq_slope arctan ordered
    continuous_arctan.continuousOn differentiable_arctan.differentiableOn
  have lower := (abs_le.mp u_bound).1.trans between.1.le
  have upper := between.2.le.trans (abs_le.mp v_bound).2
  have small : c ^ 2 ≤ (0.338 : ℝ) ^ 2 := by
    have squared := pow_le_pow_left₀ (abs_nonneg c) (abs_le.mpr ⟨lower, upper⟩) 2
    rwa [sq_abs] at squared
  rw [Real.deriv_arctan] at derivative
  change 1 / (1 + c ^ 2) = (arctan v - arctan u) / (v - u) at derivative
  have deriv_lower : 0.897 < 1 / (1 + c ^ 2) :=
    (lt_div_iff₀ (by positivity)).mpr (by linarith only [small])
  rw [derivative] at deriv_lower
  exact (lt_div_iff₀ (sub_pos.mpr ordered)).mp deriv_lower

/-- The indicated complex tangent vector is the altitude times its signed slope ray. -/
private theorem aperture_lift {x h : ℝ} (positive : 0 < h) :
    (⟨x, h⟩ : ℂ) = Complex.I * (h • slopeRay (-x / h)) := by
  apply Complex.ext
  · simp [Complex.mul_re, slopeRay, Complex.smul_re, smul_eq_mul]
    field_simp [positive.ne']
  · simp [Complex.mul_im, slopeRay, Complex.smul_im, smul_eq_mul]

/-- The actual planar apex angle is the difference of its two long-side arguments. -/
theorem latitude_apex_angle {left right base apex height : ℝ} (base_pos : left < right)
    (height_pos : 0 < height) :
    angle ((⟨right, base⟩ : ℂ) - ⟨apex, base - height⟩)
      ((⟨left, base⟩ : ℂ) - ⟨apex, base - height⟩) =
      arctan (latitudeWestRatio left apex height) - arctan (latitudeEastRatio right apex height) := by
  let u := latitudeEastRatio right apex height
  let v := latitudeWestRatio left apex height
  have right_lift : (⟨right, base⟩ : ℂ) - ⟨apex, base - height⟩ =
      Complex.I * (height • slopeRay u) := by
    have vertex : (⟨right, base⟩ : ℂ) - ⟨apex, base - height⟩ = ⟨right - apex, height⟩ := by
      apply Complex.ext <;> simp
    rw [vertex, aperture_lift height_pos, neg_sub]
    rfl
  have left_lift : (⟨left, base⟩ : ℂ) - ⟨apex, base - height⟩ =
      Complex.I * (height • slopeRay v) := by
    have vertex : (⟨left, base⟩ : ℂ) - ⟨apex, base - height⟩ = ⟨left - apex, height⟩ := by
      apply Complex.ext <;> simp
    rw [vertex, aperture_lift height_pos, neg_sub]
    rfl
  have compare : u < v :=
    (div_lt_div_iff_of_pos_right height_pos).mpr (sub_lt_sub_left base_pos apex)
  rw [right_lift, left_lift, Complex.angle_mul_left Complex.I_ne_zero,
    angle_smul_left_of_pos _ _ height_pos, angle_smul_right_of_pos _ _ height_pos, angle_slopeRay,
    abs_of_nonneg (sub_nonneg.mpr (arctan_mono compare.le))]

/-- The horizontal component of an incident long side controls the base-angle cosine. -/
theorem abs_cos_angle_horizontal_le_ratio (side : Bool) {z : ℂ} (vertical : z.im ≠ 0) :
    |cos (angle (if side then (-1 : ℂ) else 1) z)| ≤ |z.re| / |z.im| := by
  have genuine : z ≠ 0 := fun h => vertical (congrArg Complex.im h)
  have formula : |cos (angle (if side then (-1 : ℂ) else 1) z)| = |z.re| / ‖z‖ := by
    cases side
    · simp only [Bool.false_eq_true, ite_false, Complex.angle_one_left genuine,
        Real.cos_abs, Complex.cos_arg genuine, abs_div, abs_norm]
    · rw [ite_eq_left rfl, angle_comm, Complex.angle_eq_abs_arg genuine (by norm_num),
        div_neg, div_one, Real.cos_abs, Complex.cos_arg (neg_ne_zero.mpr genuine),
        abs_div, Complex.neg_re, abs_neg, norm_neg, abs_norm]
  rw [formula]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (abs_pos.mpr vertical) (Complex.abs_im_le_norm _)


/-- The exact short base and altitude give the required lower bound at the planar apex. -/
theorem latitude_apex_lower {a left right base apex height : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (height_pos : 0 < height)
    (width : 0.8 * spacing a < right - left) (altitude : height < 1.052 * radius a)
    (east : |latitudeEastRatio right apex height| < 1.144 * spacing a / radius a)
    (west : |latitudeWestRatio left apex height| < 1.144 * spacing a / radius a) :
    0.682 * (spacing a / radius a) <
      angle ((⟨right, base⟩ : ℂ) - ⟨apex, base - height⟩)
        ((⟨left, base⟩ : ℂ) - ⟨apex, base - height⟩) := by
  have spacing_positive := spacing_pos positive
  have rad := radius_pos positive
  have short : left < right :=
    sub_pos.mp ((mul_pos (by norm_num : 0 < (0.8 : ℝ)) spacing_positive).trans width)
  rw [latitude_apex_angle short height_pos]
  let u := latitudeEastRatio right apex height
  let v := latitudeWestRatio left apex height
  let x := spacing a / radius a
  have x_pos : 0 < x := div_pos spacing_positive rad
  have exact_ratio : x = 0.56 * a := by
    dsimp [x, spacing]
    field_simp [rad.ne']
  have a_small : a < 0.524 := by linarith only [small, pi_lt_d6]
  have ratio_bound : 1.144 * spacing a / radius a < 0.338 := by
    rw [mul_div_assoc]
    change 1.144 * x < 0.338
    rw [exact_ratio]
    linarith only [a_small]
  have compare : u < v :=
    (div_lt_div_iff_of_pos_right height_pos).mpr (sub_lt_sub_left short apex)
  have diff : v - u = (right - left) / height := by
    dsimp [v, u, latitudeWestRatio, latitudeEastRatio]
    rw [← sub_div]
    congr 1
    ring
  have spread := arctan_spread_lower compare (east.trans ratio_bound).le (west.trans ratio_bound).le
  have width_lower : 0.682 * x < 0.897 * (v - u) := by
    calc
      _ < (0.897 * (right - left)) / height := by
        apply (lt_div_iff₀ height_pos).mpr
        have top := mul_lt_mul_of_pos_left altitude (show 0 < 0.682 * x by positivity)
        have bottom := mul_lt_mul_of_pos_left width (show 0 < (0.897 : ℝ) by norm_num)
        have scaled : x * radius a = spacing a := div_mul_cancel₀ _ rad.ne'
        nlinarith only [top, bottom, scaled, spacing_positive]
      _ = _ := by rw [diff, mul_div_assoc]
  exact width_lower.trans spread

/-- Sine loss under the gnomonic chart bounds still leaves the required actual apex margin. -/
theorem annular_apex_halfSine_of_angle {x θ : ℝ} (x_pos : 0 < x) (x_small : x ≤ 0.294)
    (angle_lower : 0.682 * x ≤ θ) (angle_upper : θ ≤ π) :
    0.334 * x < 0.982 * sin (θ / 2) := by
  let t := 0.341 * x
  have t_pos : 0 < t := mul_pos (by norm_num) x_pos
  have t_small : t ≤ 0.101 := by dsimp [t]; linarith only [x_small]
  have t_le : t ≤ θ / 2 := by dsimp [t]; linarith only [angle_lower]
  have sin_bound : sin t ≤ sin (θ / 2) := strictMonoOn_sin.monotoneOn
    ⟨by linarith only [t_pos, pi_pos], by linarith only [t_small, pi_gt_three]⟩
    ⟨by linarith only [angle_lower, x_pos, pi_pos], by linarith only [angle_upper]⟩ t_le
  have sq := pow_le_pow_left₀ t_pos.le t_small 2
  have cube := mul_le_mul_of_nonneg_right sq t_pos.le
  have almost := sin_gt_sub_cube t_pos
  have lower : 0.334 * x < 0.982 * sin t := by
    nlinarith only [cube, almost, x_pos, show t = 0.341 * x from rfl]
  exact lower.trans_le (mul_le_mul_of_nonneg_left sin_bound (by norm_num))

/-- A bound on a base corner's cosine gives the required half-sine margin after projection. -/
theorem annular_base_halfSine_of_cos {θ : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ π)
    (cosine : cos θ ≤ 0.338) : 0.564 < 0.982 * sin (θ / 2) := by
  have sine : 0 ≤ sin (θ / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith only [nonnegative]) (by linarith only [small, pi_pos])
  have sq_sine : sin (θ / 2) ^ 2 = 1 / 2 - cos θ / 2 := by
    rw [sin_sq_eq_half_sub, show 2 * (θ / 2) = θ by ring]
  apply (sq_lt_sq₀ (by norm_num) (mul_nonneg (by norm_num) sine)).mp
  rw [mul_pow]
  nlinarith only [sq_sine, cosine]


/-- The two actual planar base corners satisfy the half-sine estimate for the chart distortion. -/
theorem latitude_base_halfSines {left right base apex height : ℝ} (base_pos : left < right)
    (height_pos : 0 < height) (east : |latitudeEastRatio right apex height| ≤ 0.338)
    (west : |latitudeWestRatio left apex height| ≤ 0.338) :
    let L : ℂ := ⟨left, base⟩
    let R : ℂ := ⟨right, base⟩
    let A : ℂ := ⟨apex, base - height⟩
    0.564 < 0.982 * sin (angle (R - L) (A - L) / 2) ∧
      0.564 < 0.982 * sin (angle (L - R) (A - R) / 2) := by
  let L : ℂ := ⟨left, base⟩
  let R : ℂ := ⟨right, base⟩
  let A : ℂ := ⟨apex, base - height⟩
  let long (x : ℝ) := A - (⟨x, base⟩ : ℂ)
  have cosine (side : Bool) (x : ℝ) (ratio : |(apex - x) / height| ≤ 0.338) :
      cos (angle (if side then (-1 : ℂ) else 1) (long x)) ≤ 0.338 := by
    have re : (long x).re = apex - x := rfl
    have im : (long x).im = -height := by change base - height - base = _; ring
    have nonzero : (long x).im ≠ 0 := by rw [im]; exact neg_ne_zero.mpr height_pos.ne'
    have bound := abs_cos_angle_horizontal_le_ratio side nonzero
    rw [re, im, abs_neg, ← abs_div] at bound
    exact (le_abs_self _).trans (bound.trans ratio)
  have at_left : R - L = (right - left) • (1 : ℂ) := by
    apply Complex.ext <;> simp [L, R, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  have at_right : L - R = (right - left) • (-1 : ℂ) := by
    apply Complex.ext <;> simp [L, R, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  change 0.564 < 0.982 * sin (angle (R - L) (long left) / 2) ∧
    0.564 < 0.982 * sin (angle (L - R) (long right) / 2)
  rw [at_left, at_right, angle_smul_left_of_pos _ _ (sub_pos.mpr base_pos),
    angle_smul_left_of_pos _ _ (sub_pos.mpr base_pos)]
  exact ⟨annular_base_halfSine_of_cos (angle_nonneg _ _) (angle_le_pi _ _) (cosine false left west),
    annular_base_halfSine_of_cos (angle_nonneg _ _) (angle_le_pi _ _) (cosine true right east)⟩

end Unfoldings.FewestNets.AcuteLatitudeGrid
