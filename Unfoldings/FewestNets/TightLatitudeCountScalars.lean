module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars

/-! Scalar constants for the tightened latitude-grid count. -/

@[expose] public section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- Concavity gives the paper's lower bound for the sine of the input angle. -/
theorem sine_input_lower_tight {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    1.6532 * a < sin (2 * a) := by
  let t := 6 * a / π
  have t_pos : 0 < t := by dsimp [t]; positivity
  have t_le : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one pi_pos).mpr
    linarith only [small]
  have cap := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show π / 3 ∈ Set.Icc (0 : ℝ) π from
      ⟨by positivity, by linarith only [pi_pos]⟩)
    (sub_nonneg.mpr t_le) t_pos.le (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero] at cap
  rw [sin_pi_div_three] at cap
  have parameter : t * (π / 3) = 2 * a := by
    dsimp [t]
    field_simp [pi_ne_zero]
    ring
  rw [parameter] at cap
  have root : (1.73205 : ℝ) < √3 := by
    apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by norm_num)]
    norm_num
  have factor : 1.6532 * π < 3 * √3 := by
    linarith only [root, pi_lt_d6]
  apply lt_of_lt_of_le _ cap
  have h := mul_lt_mul_of_pos_right factor positive
  apply (mul_lt_mul_iff_of_pos_right pi_pos).mp
  dsimp only [t]
  convert h using 1 <;> field_simp [pi_ne_zero] <;> ring

/-- The common coefficient of the two Crofton charge bounds. -/
theorem local_count_prefactor_tight {a s : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (nonnegative : 0 ≤ s) (short : s ≤ 0.115) :
    2 / (cos (s / 2) ^ 2 * sin (2 * a)) < 1.2138 / a := by
  have half : s / 2 ≤ 0.0575 := by linarith only [short]
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ s / 2) half 2
  have cos_lower : 0.998346875 ≤ cos (s / 2) := by
    linarith only [sq, one_sub_sq_div_two_le_cos (x := s / 2)]
  have cos_square := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.998346875) cos_lower 2
  have sine := sine_input_lower_tight positive small
  have sine_pos : 0 < sin (2 * a) := (mul_pos (by norm_num) positive).trans sine
  have cosine_pos : 0 < cos (s / 2) := (by norm_num : (0 : ℝ) < 0.998346875).trans_le cos_lower
  apply (div_lt_div_iff₀ (mul_pos (pow_pos cosine_pos 2) sine_pos) positive).mpr
  have combined := mul_lt_mul_of_pos_left sine
    (show 0 < (0.998346875 : ℝ) ^ 2 by positivity)
  have lower := mul_le_mul_of_nonneg_right cos_square sine_pos.le
  nlinarith only [combined, lower, positive]

end Unfoldings.FewestNets.AcuteLatitudeGrid

namespace Unfoldings.FewestNets

/-- The normalized count polynomial on the analytic range of the tightened estimate. -/
theorem tightLatitude_small_coefficient_lt {a : ℝ} (positive : 0 < a) (small : a ≤ 0.31) :
    2 * a ^ 4 + 4.90 * a ^ 2 + 1.2138 * 0.674 *
      ((1.168 - 0.089 * a) * (99.71 - 3.22 * a) / 0.51 +
        (2 + 0.2212 * a ^ 2) * 116.8 * a + (0.03 * 29 + 1.545 * 6.3) * a / 0.51) < 246.3 := by
  let K : ℝ := 1.2138 * 0.674
  let constant := K * (1.168 * 99.71 / 0.51)
  let linear := K * ((0.03 * 29 + 1.545 * 6.3 - 1.168 * 3.22 - 0.089 * 99.71) / 0.51 + 2 * 116.8)
  let quadratic := 4.90 + K * (0.089 * 3.22 / 0.51)
  let cubic := K * (0.2212 * 116.8)
  have exp : 2 * a ^ 4 + 4.90 * a ^ 2 + 1.2138 * 0.674 *
      ((1.168 - 0.089 * a) * (99.71 - 3.22 * a) / 0.51 +
        (2 + 0.2212 * a ^ 2) * 116.8 * a + (0.03 * 29 + 1.545 * 6.3) * a / 0.51) =
      constant + linear * a + quadratic * a ^ 2 + cubic * a ^ 3 + 2 * a ^ 4 := by
    dsimp only [constant, linear, quadratic, cubic, K]
    ring
  have l : 0 ≤ linear := by norm_num [linear, K]
  have q : 0 ≤ quadratic := by norm_num [quadratic, K]
  have c : 0 ≤ cubic := by norm_num [cubic, K]
  rw [exp]
  calc
    _ ≤ constant + linear * 0.31 + quadratic * 0.31 ^ 2 + cubic * 0.31 ^ 3 + 2 * 0.31 ^ 4 := by
      gcongr <;> exact positive.le
    _ < 246.3 := by norm_num [constant, linear, quadratic, cubic, K]

end Unfoldings.FewestNets
