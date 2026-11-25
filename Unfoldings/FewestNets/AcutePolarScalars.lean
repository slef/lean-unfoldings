module

public import Unfoldings.FewestNets.RoundSelectorScalars

/-! The actual wider latitude rows still give the required round polar aperture and exits. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- At the revised polar side count, the progress cone is wide enough for the original edges. -/
theorem acute_polar_cone_ratio_lt {a x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (nonnegative : 0 ≤ x) (sixth : x ≤ π / 6) (mesh : x ≤ 1.09 * a) :
    1 / (√2 * cos x) < cos (π / 4 - 0.49 * a) := by
  have a_small : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have x_small : x ≤ 0.524 := by linarith only [sixth, pi_lt_d4]
  have pos_sin : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi nonnegative
    (by linarith only [sixth, pi_pos])
  have sine_bound := pow_le_pow_left₀ pos_sin (sin_le nonnegative) 2
  have sq_bound := pow_le_pow_left₀ nonnegative x_small 2
  have sin_sq : sin x ^ 2 ≤ 0.572 * a := by
    have h := mul_le_mul x_small mesh nonnegative (by norm_num : (0 : ℝ) ≤ 0.524)
    nlinarith only [sine_bound, h, positive]
  have cos_sq : (1 - (0.524 : ℝ) ^ 2) ≤ cos x ^ 2 := by
    linarith only [sin_sq_add_cos_sq x, sine_bound, sq_bound]
  have lower_sin : 0.93 * a < sin (0.98 * a) := by
    have x_pos : 0 < 0.98 * a := by positivity
    have a_sq := pow_le_pow_left₀ x_pos.le (show 0.98 * a ≤ 0.514 by
      linarith only [a_small]) 2
    have cubic := mul_le_mul_of_nonneg_right a_sq x_pos.le
    nlinarith only [sin_gt_sub_cube x_pos, cubic, positive]
  have lower : 0.572 * a < sin (0.98 * a) * cos x ^ 2 := by
    have h := mul_lt_mul_of_pos_right lower_sin
      (show 0 < (1 - (0.524 : ℝ) ^ 2) by norm_num)
    have k := mul_le_mul_of_nonneg_left cos_sq (by linarith only [lower_sin, positive])
    nlinarith only [h, k, positive]
  have enough : 1 < (1 + sin (0.98 * a)) * cos x ^ 2 := by
    nlinarith only [sin_sq_add_cos_sq x, sin_sq, lower]
  have cos_id : 2 * cos (π / 4 - 0.49 * a) ^ 2 = 1 + sin (0.98 * a) := by
    have double := cos_two_mul (π / 4 - 0.49 * a)
    rw [show 2 * (π / 4 - 0.49 * a) = π / 2 - 0.98 * a by ring, cos_pi_div_two_sub] at double
    linarith only [double]
  have cos_pos : 0 < cos x := cos_pos_of_mem_Ioo
    ⟨by linarith only [nonnegative, pi_pos], by linarith only [sixth, pi_pos]⟩
  have right_pos : 0 < cos (π / 4 - 0.49 * a) := cos_pos_of_mem_Ioo
    ⟨by linarith only [small, pi_pos], by linarith only [positive, pi_pos]⟩
  apply (sq_lt_sq₀ (by positivity : 0 ≤ 1 / (√2 * cos x)) right_pos.le).mp
  rw [div_pow, one_pow, mul_pow, sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [← cos_id] at enough
  nlinarith only [enough]

/-- A polar side within thirty degrees of its rim slope has the required radial margin. -/
theorem acute_polar_exit_margin {a x : ℝ} (small : a ≤ π / 6)
    (nonnegative : 0 ≤ x) (sixth : x ≤ π / 6) :
    0.48 * a ≤ cos (π / 4 + x) := by
  have angle_limit : π / 4 + x ≤ π / 4 + π / 6 := add_le_add_right sixth _
  have cosine := cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ π / 4 + x)
    (by linarith only [pi_pos] : π / 4 + π / 6 ≤ π) angle_limit
  have value : 0.258 < cos (π / 4 + π / 6) := by
    rw [cos_add, cos_pi_div_four, cos_pi_div_six, sin_pi_div_four, sin_pi_div_six]
    have root₂ : 1.414 < √(2 : ℝ) := by
      apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
      rw [sq_sqrt (by norm_num)]
      norm_num
    have root₃ : 1.732 < √(3 : ℝ) := by
      apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
      rw [sq_sqrt (by norm_num)]
      norm_num
    have product := mul_lt_mul_of_pos_right root₃
      (show 0 < √(2 : ℝ) by positivity)
    nlinarith only [root₂, product]
  exact (show 0.48 * a < 0.258 by linarith only [small, pi_lt_d4]).le.trans
    (value.le.trans cosine)

end Unfoldings.FewestNets
