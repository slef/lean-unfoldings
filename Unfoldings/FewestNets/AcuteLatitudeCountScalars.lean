module

public import Unfoldings.FewestNets.AcuteLatitudeRows
public import Unfoldings.Geometry.Angles
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Scalar bounds for the two local component-count estimates. -/

@[expose] public section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- If all three face angles are at most `π/2 - a`, all three are at least `2*a`. -/
theorem input_cornerAngle_lower {a : ℝ} (T : Triangle)
    (upper : ∀ i, T.cornerAngle i ≤ π / 2 - a) (i : Fin 3) :
    2 * a ≤ T.cornerAngle i := by
  have angle_sum := T.sum_cornerAngle
  rw [Fin.sum_univ_three] at angle_sum
  have first : 2 * a ≤ T.cornerAngle 0 := by linarith only [upper 1, upper 2, angle_sum]
  have second : 2 * a ≤ T.cornerAngle 1 := by linarith only [upper 0, upper 2, angle_sum]
  have third : 2 * a ≤ T.cornerAngle 2 := by linarith only [upper 0, upper 1, angle_sum]
  fin_cases i <;> assumption

/-- Concavity gives the paper's lower bound for the sine of the input angle. -/
theorem sine_input_lower {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    1.653 * a < sin (2 * a) := by
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
  have root : (1.732 : ℝ) < √3 := by
    apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by norm_num)]
    norm_num
  have factor : 1.653 * π < 3 * √3 := by
    linarith only [root, pi_lt_d4]
  apply lt_of_lt_of_le _ cap
  have h := mul_lt_mul_of_pos_right factor positive
  apply (mul_lt_mul_iff_of_pos_right pi_pos).mp
  dsimp only [t]
  convert h using 1 <;> field_simp [pi_ne_zero] <;> ring

/-- The common coefficient of the two Crofton charge bounds. -/
theorem local_count_prefactor {a s : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (nonnegative : 0 ≤ s) (short : s ≤ 0.115) :
    2 / (cos (s / 2) ^ 2 * sin (2 * a)) < 1.215 / a := by
  have half : s / 2 ≤ 0.0575 := by linarith only [short]
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ s / 2) half 2
  have cos_lower : 0.998346875 ≤ cos (s / 2) := by
    linarith only [sq, one_sub_sq_div_two_le_cos (x := s / 2)]
  have cos_square := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.998346875) cos_lower 2
  have sine := sine_input_lower positive small
  have sine_pos : 0 < sin (2 * a) := (mul_pos (by norm_num) positive).trans sine
  have cosine_pos : 0 < cos (s / 2) := (by norm_num : (0 : ℝ) < 0.998346875).trans_le cos_lower
  apply (div_lt_div_iff₀ (mul_pos (pow_pos cosine_pos 2) sine_pos) positive).mpr
  have combined := mul_lt_mul_of_pos_left sine
    (show 0 < (0.998346875 : ℝ) ^ 2 by positivity)
  have lower := mul_le_mul_of_nonneg_right cos_square sine_pos.le
  nlinarith only [combined, lower, positive]

/-- The actual bound for a triangle, once the corner and side budgets are proved. -/
theorem triangle_count_excess_lt {a factor M : ℝ} (positive : 0 < a)
    (factor_bound : factor ≤ 1.215 / a) (nonnegative : 0 ≤ M)
    (triangle_budget : M ≤ 2.462 / a) :
    factor * M < 3 / a ^ 2 := by
  apply (mul_le_mul factor_bound triangle_budget nonnegative (by positivity)).trans_lt
  rw [div_mul_div_comm, ← pow_two]
  exact div_lt_div_of_pos_right (by norm_num) (pow_pos positive 2)

/-- The actual bound for a polar polygon, once the corner and side budgets are proved. -/
theorem polar_count_excess_lt {a factor M : ℝ} {k : ℕ} (positive : 0 < a)
    (factor_bound : factor ≤ 1.215 / a) (nonnegative : 0 ≤ M)
    (polar_budget : M ≤ 2 * (k : ℝ)) (sides : (k : ℝ) < 3.5 / a) :
    factor * M < 8.51 / a ^ 2 := by
  have upper : M ≤ 7 / a := by
    have h := mul_le_mul_of_nonneg_left sides.le (show (0 : ℝ) ≤ 2 by norm_num)
    exact polar_budget.trans (h.trans_eq (by ring))
  apply (mul_le_mul factor_bound upper nonnegative (by positivity)).trans_lt
  rw [div_mul_div_comm, ← pow_two]
  exact div_lt_div_of_pos_right (by norm_num) (pow_pos positive 2)

end Unfoldings.FewestNets.AcuteLatitudeGrid
