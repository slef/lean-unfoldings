module

public import Unfoldings.FewestNets.RevisedLatitudeCountBounds

/-! Unweighted triangle count for the joint base-angle charge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The unweighted count multiplied by the square of the margin stays below
the coefficient used for the two base corners. -/
theorem triangleCount_mul_sq_lt (a : ℝ) (positive : 0 < a) (small : a ≤ π / 6) :
    (triangleCount a : ℝ) * a ^ 2 < 116.8 := by
  let r := radius a
  let b := spacing a
  let Δ := rowStep a
  let J := stripCount a
  have rp : 0 < r := radius_pos positive
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < Δ := rowStep_pos positive small
  have am : a ≤ 0.524 := by linarith only [small, pi_lt_d6]
  have asq := pow_le_pow_left₀ positive.le am 2
  have root : √a ≤ 0.724 := (sqrt_le_left (by norm_num)).mpr (am.trans (by norm_num))
  have rprod : b * r = 0.264384 * a ^ 2 := by
    change (0.51 * a * (0.72 * √a)) * (0.72 * √a) = _
    linear_combination (0.264384 * a) * sq_sqrt positive.le
  have den : 0.852 * (0.264384 * a ^ 2) ≤ b * Δ := by
    rw [← rprod, ← mul_assoc, mul_comm 0.852 b, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rowStep_bounds positive small).1.le bp.le
  have area : (8 * π * (1 - 0.034 * a) / (b * Δ)) * a ^ 2 ≤ 111.58 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos bp dp)).mpr
    have h := mul_le_mul_of_nonneg_left den (show (0 : ℝ) ≤ 111.58 by norm_num)
    have factor_pos : 0 ≤ (1 - 0.034 * a) * a ^ 2 :=
      mul_nonneg (by linarith only [am]) (sq_nonneg _)
    have top := mul_le_mul_of_nonneg_right (show 8 * π ≤ 8 * (3.141593 : ℝ) by linarith only [pi_lt_d6])
      factor_pos
    have s := mul_le_mul_of_nonneg_right
      (show 1 - 0.034 * a ≤ 1 by linarith only [positive]) (sq_nonneg a)
    nlinarith only [h, top, s, sq_nonneg a]
  have J_bound : (J : ℝ) < π / r + 1 := by
    have meridian : 0 ≤ π - 2 * AcuteLatitudeGrid.polarRadius a := by
      linarith only [pi_gt_d2, AcuteLatitudeGrid.polarRadius_lt small]
    have ceil := Nat.ceil_lt_add_one (div_nonneg meridian rp.le)
    change (J : ℝ) < (π - 2 * AcuteLatitudeGrid.polarRadius a) / r + 1 at ceil
    have hi : (π - 2 * AcuteLatitudeGrid.polarRadius a) / r ≤ π / r :=
      div_le_div_of_nonneg_right (by linarith only [AcuteLatitudeGrid.polarRadius_pos positive]) rp.le
    linarith only [ceil, hi]
  have base : (2 * (π / r)) * a ^ 2 = (2 * π / 0.72) * (√a * a) := by
    change _ = _
    dsimp only [r, radius]
    field_simp [(sqrt_pos.mpr positive).ne']
    rw [sq_sqrt positive.le]
  have jm : (2 * (J : ℝ) + 1 + 1.903 / a) * a ^ 2 ≤ 5.14 := by
    have h := mul_le_mul_of_nonneg_right J_bound.le (sq_nonneg a)
    have sb := mul_le_mul root am positive.le (by norm_num : (0 : ℝ) ≤ 0.724)
    have hb : 2 * π / (0.72 : ℝ) ≤ 8.727 :=
      (div_le_iff₀ (by norm_num)).mpr (by linarith only [pi_lt_d6])
    have upper := mul_le_mul hb sb (by positivity : 0 ≤ √a * a) (by norm_num : (0 : ℝ) ≤ 8.727)
    have cancel : (1.903 / a) * a ^ 2 = 1.903 * a := by field_simp [positive.ne']
    calc
      _ = 2 * ((J : ℝ) * a ^ 2) + a ^ 2 + (1.903 / a) * a ^ 2 := by ring
      _ ≤ 2 * ((π / r + 1) * a ^ 2) + a ^ 2 + (1.903 / a) * a ^ 2 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)) le_rfl) le_rfl
      _ = (2 * π / 0.72) * (√a * a) + 3 * a ^ 2 + 1.903 * a := by
        rw [← base, cancel]
        ring
      _ ≤ _ := by linarith only [upper, asq, am]
  have count := mul_lt_mul_of_pos_right (triangleCount_lt_rows positive small) (pow_pos positive 2)
  change (triangleCount a : ℝ) * a ^ 2 <
    ((2 * (J : ℝ) + 1 + 1.903 / a) + 8 * π * (1 - 0.034 * a) / (b * Δ)) * a ^ 2 at count
  rw [add_mul] at count
  linarith only [count, area, jm]

/-- On the seven-band range the unweighted count needs a smaller rounding allowance. -/
theorem triangleCount_mul_sq_lt_seven_bands (a : ℝ) (lower : 0.38 ≤ a) (upper : a ≤ 0.42) :
    (triangleCount a : ℝ) * a ^ 2 < 104.6 := by
  let r := radius a
  let b := spacing a
  let d := rowStep a
  let span := π - 2 * AcuteLatitudeGrid.polarRadius a
  have positive : 0 < a := by linarith only [lower]
  have small : a ≤ π / 6 := by linarith only [upper, pi_gt_three]
  have rp : 0 < r := radius_pos positive
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < d := rowStep_pos positive small
  have root_lo : 0.616 ≤ √a :=
    (le_sqrt (by norm_num) positive.le).mpr (by linarith only [lower] : (0.616 : ℝ) ^ 2 ≤ a)
  have root_hi : √a ≤ 0.6481 :=
    (sqrt_le_left (by norm_num)).mpr (upper.trans (by norm_num))
  have span_lower : 6.5 * r ≤ span := by
    dsimp only [r, span, radius, AcuteLatitudeGrid.polarRadius]
    linarith only [root_hi, pi_gt_d4]
  have span_upper : span ≤ 7 * r := by
    dsimp only [r, span, radius, AcuteLatitudeGrid.polarRadius]
    linarith only [root_lo, pi_lt_d6]
  have ql : (6 : ℝ) < span / r := (lt_div_iff₀ rp).mpr (by linarith only [span_lower, rp])
  have qu : span / r ≤ (7 : ℝ) := (div_le_iff₀ rp).mpr span_upper
  have J : stripCount a = 7 := by
    have lo : 6 < stripCount a := Nat.lt_ceil.mpr ql
    have hi : stripCount a ≤ 7 := Nat.ceil_le.mpr qu
    omega
  have step : (13 / 14 : ℝ) * r ≤ d := by
    change _ ≤ span / (stripCount a : ℝ)
    rw [J]
    push_cast
    linarith only [span_lower]
  have rprod : b * r = 0.264384 * a ^ 2 := by
    change (0.51 * a * (0.72 * √a)) * (0.72 * √a) = _
    linear_combination (0.264384 * a) * sq_sqrt positive.le
  have den : (13 / 14 : ℝ) * (0.264384 * a ^ 2) ≤ b * d := by
    rw [← rprod, ← mul_assoc, mul_comm (13 / 14 : ℝ) b, mul_assoc]
    exact mul_le_mul_of_nonneg_left step bp.le
  have area : (8 * π * (1 - 0.034 * a) / (b * d)) * a ^ 2 ≤ 101.06 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos bp dp)).mpr
    have h := mul_le_mul_of_nonneg_left den (show (0 : ℝ) ≤ 101.06 by norm_num)
    have factor_pos : 0 ≤ (1 - 0.034 * a) * a ^ 2 :=
      mul_nonneg (by linarith only [upper]) (sq_nonneg a)
    have top := mul_le_mul_of_nonneg_right (show 8 * π ≤ 8 * (3.141593 : ℝ) by linarith only [pi_lt_d6])
      factor_pos
    have s := mul_le_mul_of_nonneg_right
      (show 1 - 0.034 * a ≤ 1 - 0.034 * 0.38 by linarith only [lower]) (sq_nonneg a)
    nlinarith only [h, top, s, sq_nonneg a]
  have rows : (2 * (stripCount a : ℝ) + 1 + 1.903 / a) * a ^ 2 ≤ 3.446 := by
    have eq : (1.903 / a) * a ^ 2 = 1.903 * a := by field_simp [positive.ne']
    have asq := pow_le_pow_left₀ positive.le upper 2
    rw [J, add_mul, eq]
    norm_num1
    linarith only [asq, upper]
  have count := mul_lt_mul_of_pos_right (triangleCount_lt_rows positive small) (pow_pos positive 2)
  change (triangleCount a : ℝ) * a ^ 2 <
    ((2 * (stripCount a : ℝ) + 1 + 1.903 / a) + 8 * π * (1 - 0.034 * a) / (b * d)) * a ^ 2 at count
  rw [add_mul] at count
  linarith only [count, area, rows]

end Unfoldings.FewestNets.RevisedLatitudeGrid
