module

public import Unfoldings.FewestNets.AcuteLatitudeCountScalars

/-! The final arithmetic of the refined latitude count. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

/-- The revised band and polar estimates give the strict coefficient in the paper.
Bound the quadratic and quartic terms by their secants on `[0, 11 / 21]`. -/
theorem acute_latitude_revised_count_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    2 + 4.90 / a ^ 2 + (1.215 * 0.675) / a ^ 4 *
      ((1.225 - 0.073 * a) * (99.71 - 3.22 * a) / 0.51 + 2 * 55.9 / 0.932 +
        (0.03 * 29 + 1.545 * 6.3) * a / 0.51) < 296 / a ^ 4 := by
  let upper : ℝ := 11 / 21
  let constant : ℝ := 1.215 * 0.675 * (1.225 * 99.71 / 0.51 + 2 * 55.9 / 0.932)
  let linear : ℝ := 1.215 * 0.675 *
    ((0.03 * 29 + 1.545 * 6.3 - 1.225 * 3.22 - 0.073 * 99.71) / 0.51)
  let quadratic : ℝ := 4.90 + 1.215 * 0.675 * (0.073 * 3.22 / 0.51)
  have upper_bound : a ≤ upper := by dsimp [upper]; linarith only [small, Real.pi_lt_d6]
  have fourth : 0 < a ^ 4 := pow_pos positive _
  have square_bound : a ^ 2 ≤ upper * a := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right upper_bound positive.le
  have fourth_bound : a ^ 4 ≤ upper ^ 3 * a := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ positive.le upper_bound 3) positive.le
  have positive_quadratic : 0 < quadratic := by dsimp [quadratic]; norm_num
  apply (lt_div_iff₀ fourth).mpr
  calc
    _ = constant + linear * a + quadratic * a ^ 2 + 2 * a ^ 4 := by
      dsimp [constant, linear, quadratic]
      field_simp
      <;> ring
    _ ≤ constant + linear * a + quadratic * (upper * a) + 2 * (upper ^ 3 * a) := by
      exact add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left square_bound positive_quadratic.le) _)
        (mul_le_mul_of_nonneg_left fourth_bound (by norm_num))
    _ < 296 := by
      dsimp [constant, linear, quadratic, upper] at *
      linarith only [upper_bound, positive]

end Unfoldings.FewestNets
