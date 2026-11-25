module

public import Unfoldings.FewestNets.LatitudeMetricRows
public import Unfoldings.Geometry.SharpDevelopmentThreshold

/-! The round polar selector has sufficient aperture, progress, and squared tilt. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The nearest-side angle bounds the inverse cosine defining the minimum
polar cone aperture. -/
theorem round_selector_cone_ratio_lt {a x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (x_nonneg : 0 ≤ x) (mesh : x ^ 2 ≤ a / 4) :
    1 / (√2 * cos x) < cos (π / 4 - a / 4) := by
  have a_upper : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have x_upper : x < 0.363 := by nlinarith only [a_upper, mesh, sq_nonneg (x - 0.363)]
  have sine_x_nonneg := sin_nonneg_of_nonneg_of_le_pi x_nonneg
    (by linarith only [x_upper, pi_gt_d2])
  have sin_sq := pow_le_pow_left₀ sine_x_nonneg (Real.sin_le x_nonneg) 2
  have cos_sq : 1 - a / 4 ≤ cos x ^ 2 := by
    nlinarith only [sin_sq_add_cos_sq x, sin_sq, mesh]
  have lower := Real.mul_le_sin (by positivity : 0 ≤ a / 2)
    (by linarith only [small, pi_pos])
  have sine_a : a / π ≤ sin (a / 2) := by
    convert lower using 1 <;> ring
  have ratio : a / (4 - a) < a / π :=
    div_lt_div_of_pos_left positive pi_pos (by linarith only [a_upper, pi_lt_d4])
  have scaled := mul_lt_mul_of_pos_right (ratio.trans_le sine_a)
    (show 0 < 1 - a / 4 by linarith only [a_upper])
  have equal : a / (4 - a) * (1 - a / 4) = a / 4 := by
    have denominator : 4 - a ≠ 0 := by linarith only [a_upper]
    field_simp [denominator] <;> ring
  rw [equal] at scaled
  have sine_a_nonneg := (div_nonneg positive.le pi_pos.le).trans sine_a
  have mult := mul_le_mul_of_nonneg_right cos_sq
    (show 0 ≤ 1 + sin (a / 2) by positivity)
  have enough : 1 < (1 + sin (a / 2)) * cos x ^ 2 := by
    nlinarith only [mult, scaled]
  have cos_id : 2 * cos (π / 4 - a / 4) ^ 2 = 1 + sin (a / 2) := by
    have double := cos_two_mul (π / 4 - a / 4)
    rw [show 2 * (π / 4 - a / 4) = π / 2 - a / 2 by ring, cos_pi_div_two_sub] at double
    linarith only [double]
  have xcos_pos : 0 < cos x := cos_pos_of_mem_Ioo
    ⟨by linarith only [x_nonneg, pi_pos], by linarith only [x_upper, pi_gt_d2]⟩
  have acos_pos : 0 < cos (π / 4 - a / 4) := cos_pos_of_mem_Ioo
    ⟨by linarith only [small, pi_pos], by linarith only [positive, pi_pos]⟩
  apply (sq_lt_sq₀ (by positivity : 0 ≤ 1 / (√2 * cos x)) acos_pos.le).mp
  rw [div_pow, one_pow, mul_pow, sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  apply (div_lt_iff₀ (by positivity)).mpr
  rw [← cos_id] at enough
  nlinarith only [enough]

/-- The polar margin fits both the interior steps and the side-normal exits. -/
theorem round_selector_margin {a x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (x_nonneg : 0 ≤ x) (mesh : x ^ 2 ≤ a / 4) :
    0.48 * a ≤ sin (0.495 * a) ∧ 0.48 * a ≤ cos (π / 4 + x) ∧ 0.48 * a ≤ 0.26 := by
  have a_upper : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have x_upper : x < 0.363 := by nlinarith only [a_upper, mesh, sq_nonneg (x - 0.363)]
  have x_max : π / 4 + x ≤ 1.15 := by linarith only [x_upper, pi_lt_d4]
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ π / 4 + x) x_max 2
  have h : 0 ≤ 0.495 * a := by positivity
  have cubic := pow_le_pow_left₀ h (show 0.495 * a ≤ 0.26 by linarith only [a_upper]) 2
  have cubic := mul_le_mul_of_nonneg_right cubic h
  have sine := abs_sub_sin_le (0.495 * a)
  rw [abs_of_nonneg h] at sine
  refine ⟨?_, ?_, by linarith only [a_upper]⟩
  · nlinarith only [(abs_le.mp sine).2, cubic, positive]
  · linarith only [one_sub_sq_div_two_le_cos (x := π / 4 + x), sq, a_upper]

end Unfoldings.FewestNets
