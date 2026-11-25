module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit corner and perimeter allowances for the revised latitude selectors. -/

@[expose] public section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- A half-angle sine lower bound controls the sine of the angle capped at a right angle. -/
theorem capped_sine_lower {θ h : ℝ} (θ_nonneg : 0 ≤ θ) (θ_le : θ ≤ π)
    (h_nonneg : 0 ≤ h) (h_small : h ^ 2 ≤ 1 / 2) (bound : h ≤ sin (θ / 2)) :
    2 * h * √(1 - h ^ 2) ≤ sin (min θ (π / 2)) := by
  have root : 0 ≤ 1 - h ^ 2 := by linarith only [h_small]
  have value_nonneg : 0 ≤ 2 * h * √(1 - h ^ 2) := by positivity
  have square : (2 * h * √(1 - h ^ 2)) ^ 2 = 4 * h ^ 2 * (1 - h ^ 2) := by
    rw [mul_pow, sq_sqrt root]
    ring
  rcases le_total θ (π / 2) with small | large
  · rw [min_eq_left small]
    have sine_small : sin (θ / 2) ≤ sin (π / 4) :=
      strictMonoOn_sin.monotoneOn
        ⟨by linarith only [θ_nonneg, pi_pos], by linarith only [small, pi_pos]⟩
        ⟨by linarith only [pi_pos], by linarith only [pi_pos]⟩ (by linarith only [small])
    have sine_nonneg : 0 ≤ sin (θ / 2) := h_nonneg.trans bound
    have sine_square := pow_le_pow_left₀ sine_nonneg sine_small 2
    rw [sin_pi_div_four, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at sine_square
    have compare := pow_le_pow_left₀ h_nonneg bound 2
    have product := mul_nonneg (sub_nonneg.mpr compare)
      (show 0 ≤ 1 - sin (θ / 2) ^ 2 - h ^ 2 by linarith only [sine_square, h_small])
    have identity : sin θ ^ 2 = 4 * sin (θ / 2) ^ 2 * (1 - sin (θ / 2) ^ 2) := by
      conv_lhs => rw [show θ = 2 * (θ / 2) by ring, sin_two_mul]
      nlinarith only [congrArg (fun z => (4 * sin (θ / 2) ^ 2) * z)
        (sin_sq_add_cos_sq (θ / 2))]
    apply (sq_le_sq₀ value_nonneg (sin_nonneg_of_nonneg_of_le_pi θ_nonneg θ_le)).mp
    rw [square, identity]
    nlinarith only [product]
  · rw [min_eq_right large, sin_pi_div_two]
    apply (sq_le_sq₀ value_nonneg zero_le_one).mp
    rw [square]
    nlinarith only [sq_nonneg (2 * h ^ 2 - 1)]

/-- The two base corners have enough half-angle sine for the capped Crofton factor. -/
theorem tri_base_capped_sine {θ : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ π)
    (bound : 0.564 ≤ sin (θ / 2)) : 0.93 < sin (min θ (π / 2)) := by
  apply lt_of_lt_of_le _ (capped_sine_lower nonnegative small
    (by norm_num : (0 : ℝ) ≤ 0.564) (by norm_num) bound)
  apply (sq_lt_sq₀ (by norm_num) (by positivity)).mp
  rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 - 0.564 ^ 2)]
  norm_num

/-- The apex capped sine is at least the required multiple of the spacing ratio. -/
theorem tri_apex_capped_sine {θ x : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ π)
    (x_pos : 0 < x) (x_small : x ≤ 0.294) (bound : 0.334 * x ≤ sin (θ / 2)) :
    0.664 * x < sin (min θ (π / 2)) := by
  have x_sq := pow_le_pow_left₀ x_pos.le x_small 2
  have h_sq : (0.334 * x) ^ 2 ≤ 1 / 2 := by
    rw [mul_pow]
    linarith only [x_sq]
  have root : 0.995 < √(1 - (0.334 * x) ^ 2) := by
    have radicand : 0 ≤ 1 - (0.334 * x) ^ 2 := by linarith only [h_sq]
    apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt radicand, mul_pow]
    linarith only [x_sq]
  apply lt_of_lt_of_le _ (capped_sine_lower nonnegative small (by positivity) h_sq bound)
  nlinarith only [mul_lt_mul_of_pos_left root x_pos, x_pos]

/-- The longest side of an annular cell contributes at most the paper's coefficient. -/
theorem tri_longest_side_factor {l : ℝ} (positive : 0 < l) (small : l ≤ 0.266) :
    2 * l / (π * sin l) < 0.645 := by
  have sine_pos := sin_pos_of_pos_of_lt_pi positive (by linarith only [small, pi_gt_d2])
  have l_sq := pow_le_pow_left₀ positive.le small 2
  have sine_lower := sin_gt_sub_cube positive
  have scale : l * (1 - (0.266 : ℝ) ^ 2 / 6) < sin l := by
    have h := mul_le_mul_of_nonneg_left l_sq positive.le
    nlinarith only [h, sine_lower]
  apply (div_lt_iff₀ (mul_pos pi_pos sine_pos)).mpr
  have first := mul_lt_mul_of_pos_left scale (show 0 < 0.645 * π by positivity)
  have second := mul_lt_mul_of_pos_right pi_gt_d2 positive
  nlinarith only [first, second, positive]

/-- The annular corner cutoffs and perimeter are both below the required budget. -/
theorem tri_count_max_lt {a b₀ b₁ b₂ L : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (apex : b₀ ≤ 0.645 / (0.664 * 0.56 * a))
    (base₁ : b₁ ≤ 0.645 / 0.93) (base₂ : b₂ ≤ 0.645 / 0.93)
    (perimeter : L ≤ 6 * (0.568 * radius a)) :
    max (b₀ + b₁ + b₂) (L / (π * (1 / 10))) < 2.462 / a := by
  apply max_lt
  · apply (lt_div_iff₀ positive).mpr
    have first := mul_le_mul_of_nonneg_right apex positive.le
    have cancel : 0.645 / (0.664 * 0.56 * a) * a = 0.645 / (0.664 * 0.56) := by
      rw [← div_div, div_mul_cancel₀ _ positive.ne']
    rw [cancel] at first
    have limit : a < 0.524 := by linarith only [small, pi_lt_d4]
    nlinarith only [first, mul_le_mul_of_nonneg_right base₁ positive.le,
      mul_le_mul_of_nonneg_right base₂ positive.le, limit]
  · apply (div_lt_div_iff₀ (by positivity : 0 < π * (1 / 10)) positive).mpr
    have size := radius_lt small
    have L_max : L < 0.8 := by linarith only [perimeter, size]
    have a_max : a < 0.524 := by linarith only [small, pi_lt_d4]
    have scaled := mul_lt_mul_of_pos_right L_max positive
    nlinarith only [scaled, a_max, pi_gt_d2]

end Unfoldings.FewestNets.AcuteLatitudeGrid
