module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars
public import Unfoldings.FewestNets.TaylorEnclosures

/-! Scalar bounds on the two analytic ranges of the refined latitude count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

private theorem sine_input_lower_of_endpoint {a limit slope : ℝ} (positive : 0 < a)
    (bound : a ≤ limit) (cut : 2 * limit ≤ π) (endpoint : slope * limit < sin (2 * limit)) :
    slope * a < sin (2 * a) := by
  have lp := positive.trans_le bound
  let t := a / limit
  have tp : 0 < t := div_pos positive lp
  have tu : t ≤ 1 := (div_le_one lp).mpr bound
  have chord := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show 2 * limit ∈ Set.Icc (0 : ℝ) π from ⟨by positivity, cut⟩)
    (sub_nonneg.mpr tu) tp.le (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero] at chord
  have ht : t * (2 * limit) = 2 * a := by dsimp only [t]; field_simp [lp.ne'] <;> ring
  rw [ht] at chord
  calc
    slope * a = t * (slope * limit) := by dsimp only [t]; field_simp [lp.ne'] <;> ring
    _ < t * sin (2 * limit) := mul_lt_mul_of_pos_left endpoint tp
    _ ≤ _ := chord

private theorem local_count_prefactor_of_sine {a s slope coefficient : ℝ} (positive : 0 < a)
    (nonnegative : 0 ≤ s) (short : s ≤ 0.115) (sp : 0 < slope) (cp : 0 < coefficient)
    (sine : slope * a < sin (2 * a))
    (scalar : 2 ≤ coefficient * (0.998346875 ^ 2 * slope)) :
    2 / (cos (s / 2) ^ 2 * sin (2 * a)) < coefficient / a := by
  have half : s / 2 ≤ 0.0575 := by linarith only [short]
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ s / 2) half 2
  have cos_lower : 0.998346875 ≤ cos (s / 2) := by
    linarith only [sq, one_sub_sq_div_two_le_cos (x := s / 2)]
  have ck : 0 < (0.998346875 : ℝ) := by norm_num
  have cos_square := pow_le_pow_left₀ ck.le cos_lower 2
  have sine_pos : 0 < sin (2 * a) := (mul_pos sp positive).trans sine
  have cosine_pos : 0 < cos (s / 2) := ck.trans_le cos_lower
  apply (div_lt_div_iff₀ (mul_pos (pow_pos cosine_pos 2) sine_pos) positive).mpr
  calc
    _ ≤ (coefficient * (0.998346875 ^ 2 * slope)) * a :=
      mul_le_mul_of_nonneg_right scalar positive.le
    _ = coefficient * (0.998346875 ^ 2 * (slope * a)) := by ring
    _ < coefficient * (0.998346875 ^ 2 * sin (2 * a)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left sine (pow_pos ck 2)) cp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cos_square sine_pos.le) cp.le

def tightAnalyticPrefactorScale (a : ℝ) : ℝ := if a ≤ 0.38 then 1.108 else 1.133

theorem tightAnalyticPrefactorScale_pos (a : ℝ) : 0 < tightAnalyticPrefactorScale a := by
  unfold tightAnalyticPrefactorScale
  split_ifs <;> norm_num

/-- The sharper angular factors for the small-angle and seven-band ranges. -/
theorem local_count_prefactor_tight {a s : ℝ} (positive : 0 < a) (small : a ≤ 0.42)
    (nonnegative : 0 ≤ s) (short : s ≤ 0.115) :
    2 / (cos (s / 2) ^ 2 * sin (2 * a)) < tightAnalyticPrefactorScale a / a := by
  unfold tightAnalyticPrefactorScale
  split_ifs with low
  · have sine : 1.8125 * a < sin (2 * a) := by
      apply sine_input_lower_of_endpoint positive low (by linarith only [pi_gt_three])
      have tail := (abs_le.mp (abs_sin_sub_integerTaylor_le 7 (0.76 : ℝ))).1
      norm_num [integerTaylor, sinCoefficient, Finset.sum_range_succ] at tail
      norm_num1
      linarith only [tail]
    exact local_count_prefactor_of_sine positive nonnegative short (by norm_num) (by norm_num) sine (by norm_num)
  · have sine : 1.7725 * a < sin (2 * a) := by
      apply sine_input_lower_of_endpoint positive small (by linarith only [pi_gt_three])
      have tail := (abs_le.mp (abs_sin_sub_integerTaylor_le 7 (0.84 : ℝ))).1
      norm_num [integerTaylor, sinCoefficient, Finset.sum_range_succ] at tail
      norm_num1
      linarith only [tail]
    exact local_count_prefactor_of_sine positive nonnegative short (by norm_num) (by norm_num) sine (by norm_num)

end Unfoldings.FewestNets.AcuteLatitudeGrid

namespace Unfoldings.FewestNets

open AcuteLatitudeGrid (tightAnalyticPrefactorScale)

def tightAnalyticTriangleCountCoefficient (a : ℝ) : ℝ := if a ≤ 0.38 then 116.8 else 104.6

/-- Normalized upper bound after the corner charges and triangle counts are summed. -/
def tightAnalyticCountPolynomial (a f m : ℝ) : ℝ :=
  2 * a ^ 4 + 4.90 * a ^ 2 + f * 0.674 *
    ((1.189 - 0.089 * a) * (99.71 - 3.22 * a) / 0.51 +
      (2 + 0.2212 * a ^ 2) * m * a + (0.03 * 29 + 1.545 * 6.3) * a / 0.51)

private theorem tightAnalyticCountPolynomial_mono {a limit f m : ℝ}
    (positive : 0 < a) (limit_upper : a ≤ limit) (fp : 0 ≤ f) (mp : 3 ≤ m) :
    tightAnalyticCountPolynomial a f m ≤ tightAnalyticCountPolynomial limit f m := by
  let K : ℝ := f * 0.674
  let constant := K * (1.189 * 99.71 / 0.51)
  let linear := K * ((0.03 * 29 + 1.545 * 6.3 - 1.189 * 3.22 - 0.089 * 99.71) / 0.51 + 2 * m)
  let quadratic := 4.90 + K * (0.089 * 3.22 / 0.51)
  let cubic := K * (0.2212 * m)
  have exp (x : ℝ) : tightAnalyticCountPolynomial x f m =
      constant + linear * x + quadratic * x ^ 2 + cubic * x ^ 3 + 2 * x ^ 4 := by
    unfold tightAnalyticCountPolynomial
    dsimp only [constant, linear, quadratic, cubic, K]
    ring
  have kp : 0 ≤ K := by dsimp only [K]; positivity
  have mn : 0 ≤ m := by linarith only [mp]
  have l : 0 ≤ linear := mul_nonneg kp (by linarith only [mp])
  have q : 0 ≤ quadratic := by dsimp only [quadratic]; positivity
  have c : 0 ≤ cubic := by dsimp only [cubic]; positivity
  rw [exp a, exp limit]
  gcongr <;> exact positive.le

theorem tightLatitude_small_coefficient_lt {a : ℝ} (positive : 0 < a) (small : a ≤ 0.42) :
    tightAnalyticCountPolynomial a (tightAnalyticPrefactorScale a) (tightAnalyticTriangleCountCoefficient a) <
      246.3 := by
  by_cases low : a ≤ 0.38
  · simp only [tightAnalyticPrefactorScale, tightAnalyticTriangleCountCoefficient, ite_eq_left low]
    exact (tightAnalyticCountPolynomial_mono positive low (by norm_num) (by norm_num)).trans_lt
      (by norm_num [tightAnalyticCountPolynomial])
  · simp only [tightAnalyticPrefactorScale, tightAnalyticTriangleCountCoefficient, ite_eq_right low]
    exact (tightAnalyticCountPolynomial_mono positive small (by norm_num) (by norm_num)).trans_lt
      (by norm_num [tightAnalyticCountPolynomial])

end Unfoldings.FewestNets
