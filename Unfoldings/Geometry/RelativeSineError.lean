module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith

/-! Turn an additive angle estimate and a near-unit sine ratio into a relative angle estimate. -/

@[expose] public section

namespace Unfoldings

/-- The small-angle case uses sine ratios; away from zero the additive estimate suffices. -/
theorem abs_angle_sub_le_relative_of_sine_bounds {a b r ε : ℝ}
    (positive : 0 < r) (small : r ≤ 1 / 8) (tolerance : 4 * r ≤ ε)
    (an : 0 ≤ a) (bn : 0 ≤ b) (close : |a - b| ≤ r ^ 2)
    (first : (1 - r) * Real.sin a ≤ Real.sin b)
    (last : (1 - r) * Real.sin b ≤ Real.sin a) : |a - b| ≤ ε * b := by
  by_cases large : r ≤ b
  · apply close.trans
    have square : r ^ 2 ≤ 4 * r * b := by nlinarith
    exact square.trans (mul_le_mul_of_nonneg_right tolerance bn)
  · have bsmall : b < r := lt_of_not_ge large
    have asmall : a ≤ 2 * r := by
      have upper := (abs_le.mp close).2
      nlinarith
    have linear (z : ℝ) (nonnegative : 0 ≤ z) (upper : z ≤ 2 * r) :
        (1 - r) * z ≤ Real.sin z := by
      have square : z ^ 2 ≤ r := by
        have bound : z ^ 2 ≤ (2 * r) ^ 2 :=
          (sq_le_sq₀ nonnegative (by positivity)).mpr upper
        nlinarith
      have cube : z ^ 3 ≤ r * z := by
        nlinarith [mul_le_mul_of_nonneg_right square nonnegative]
      nlinarith [Real.sin_ge_sub_cube nonnegative]
    have factor : 0 ≤ 1 - r := by linarith
    have a_lower := linear a an asmall
    have b_lower := linear b bn (by linarith)
    have a_bound : (1 - r) ^ 2 * a ≤ b := by
      have lower := mul_le_mul_of_nonneg_left a_lower factor
      nlinarith [Real.sin_le bn]
    have b_bound : (1 - r) ^ 2 * b ≤ a := by
      have lower := mul_le_mul_of_nonneg_left b_lower factor
      nlinarith [Real.sin_le an]
    have coefficient : 1 ≤ (1 + 4 * r) * (1 - r) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg r) positive.le]
    have upper : a ≤ (1 + 4 * r) * b := by
      calc
        a ≤ ((1 + 4 * r) * (1 - r) ^ 2) * a :=
          le_mul_of_one_le_left an coefficient
        _ = (1 + 4 * r) * ((1 - r) ^ 2 * a) := by ring
        _ ≤ (1 + 4 * r) * b := mul_le_mul_of_nonneg_left a_bound (by positivity)
    have lower : (1 - 4 * r) * b ≤ a := by
      have difference : (1 - 4 * r) * b ≤ (1 - r) ^ 2 * b := by
        nlinarith [mul_nonneg (sq_nonneg r) bn, mul_nonneg positive.le bn]
      exact difference.trans b_bound
    have relative : |a - b| ≤ 4 * r * b := by
      rw [abs_le]
      constructor <;> linarith
    exact relative.trans (mul_le_mul_of_nonneg_right tolerance bn)

end Unfoldings
