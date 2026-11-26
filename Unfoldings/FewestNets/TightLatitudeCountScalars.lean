module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars
public import Unfoldings.FewestNets.TaylorEnclosures

/-! Scalar constants for the tightened latitude-grid count. -/

@[expose] public section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- A chord of sine on the analytic range gives a uniform linear lower bound. -/
theorem sine_input_lower_tight {a : ℝ} (positive : 0 < a) (small : a ≤ 0.40) :
    1.7925 * a < sin (2 * a) := by
  have endpoint : (0.717 : ℝ) < sin 0.8 := by
    have tail := (abs_le.mp (abs_sin_sub_integerTaylor_le 7 (0.8 : ℝ))).1
    norm_num [integerTaylor, sinCoefficient, Finset.sum_range_succ] at tail
    linarith only [tail]
  let t := (5 / 2 : ℝ) * a
  have tp : 0 < t := by dsimp only [t]; positivity
  have tu : t ≤ 1 := by dsimp only [t]; linarith only [small]
  have chord := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show (0.8 : ℝ) ∈ Set.Icc 0 π from ⟨by norm_num, by linarith only [pi_gt_three]⟩)
    (sub_nonneg.mpr tu) tp.le (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero] at chord
  have ht : t * 0.8 = 2 * a := by dsimp only [t]; ring
  rw [ht] at chord
  have b := mul_lt_mul_of_pos_left endpoint tp
  dsimp only [t] at b chord
  linarith only [b, chord]

/-- The common coefficient of the two Crofton charge bounds. -/
theorem local_count_prefactor_tight {a s : ℝ} (positive : 0 < a) (small : a ≤ 0.40)
    (nonnegative : 0 ≤ s) (short : s ≤ 0.115) :
    2 / (cos (s / 2) ^ 2 * sin (2 * a)) < 1.12 / a := by
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
theorem tightLatitude_small_coefficient_lt {a : ℝ} (positive : 0 < a) (small : a ≤ 0.40) :
    2 * a ^ 4 + 4.90 * a ^ 2 + 1.12 * 0.674 *
      ((1.182 - 0.089 * a) * (99.71 - 3.22 * a) / 0.51 +
        (2 + 0.2212 * a ^ 2) * 116.8 * a + (0.03 * 29 + 1.545 * 6.3) * a / 0.51) < 246.3 := by
  let K : ℝ := 1.12 * 0.674
  let constant := K * (1.182 * 99.71 / 0.51)
  let linear := K * ((0.03 * 29 + 1.545 * 6.3 - 1.182 * 3.22 - 0.089 * 99.71) / 0.51 + 2 * 116.8)
  let quadratic := 4.90 + K * (0.089 * 3.22 / 0.51)
  let cubic := K * (0.2212 * 116.8)
  have exp : 2 * a ^ 4 + 4.90 * a ^ 2 + 1.12 * 0.674 *
      ((1.182 - 0.089 * a) * (99.71 - 3.22 * a) / 0.51 +
        (2 + 0.2212 * a ^ 2) * 116.8 * a + (0.03 * 29 + 1.545 * 6.3) * a / 0.51) =
      constant + linear * a + quadratic * a ^ 2 + cubic * a ^ 3 + 2 * a ^ 4 := by
    dsimp only [constant, linear, quadratic, cubic, K]
    ring
  have l : 0 ≤ linear := by norm_num [linear, K]
  have q : 0 ≤ quadratic := by norm_num [quadratic, K]
  have c : 0 ≤ cubic := by norm_num [cubic, K]
  rw [exp]
  calc
    _ ≤ constant + linear * 0.40 + quadratic * 0.40 ^ 2 + cubic * 0.40 ^ 3 + 2 * 0.40 ^ 4 := by
      gcongr <;> exact positive.le
    _ < 246.3 := by norm_num [constant, linear, quadratic, cubic, K]

end Unfoldings.FewestNets
