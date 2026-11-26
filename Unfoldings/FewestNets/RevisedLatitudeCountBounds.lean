module

public import Unfoldings.FewestNets.RevisedLatitudeMeshCount

/-! The two different weightings of the annular triangle count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

variable {a : ℝ}

private theorem scale_product (positive : 0 < a) : spacing a * radius a = 0.264384 * a ^ 2 := by
  unfold spacing radius
  calc
    _ = 0.264384 * a ^ 2 * (√a ^ 2 / a) := by field_simp; ring
    _ = _ := by rw [sq_sqrt positive.le, div_self positive.ne', mul_one]

private theorem count_mul_step (positive : 0 < a) (small : a ≤ π / 6) :
    (stripCount a : ℝ) * rowStep a = π - 2 * AcuteLatitudeGrid.polarRadius a := by
  have nz : (stripCount a : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (stripCount_pos positive small)).ne'
  unfold rowStep
  exact mul_div_cancel₀ _ nz

private theorem radius_root_upper (small : a ≤ π / 6) : √a < 0.724 := by
  apply (sqrt_lt' (by norm_num)).mpr
  have pi_upper : π < 3.141593 := pi_lt_d6
  linarith only [small, pi_upper]

/-- The apex charges carry one power of the latitude-strip height. -/
theorem triangleCount_times_relative_step_lt (positive : 0 < a) (small : a ≤ π / 6) :
    (triangleCount a : ℝ) * rowStep a / radius a < (99.71 - 3.22 * a) / a ^ 2 := by
  let r := radius a
  let b := spacing a
  let Δ := rowStep a
  let J := stripCount a
  have rp : 0 < r := radius_pos positive
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < Δ := rowStep_pos positive small
  have ap : 0 < a ^ 2 := pow_pos positive 2
  have rel := (rowStep_bounds positive small).2
  have amax : a ≤ 0.524 := by
    have pi_upper : π < 3.141593 := pi_lt_d6
    linarith only [small, pi_upper]
  have prod : b * r = 0.264384 * a ^ 2 := scale_product positive
  have pure :
      8 * π * (1 - 0.034 * a) / (b * Δ) * Δ / r * a ^ 2 =
        (8 * π / 0.264384) * (1 - 0.034 * a) := by
    calc
      _ = 8 * π * (1 - 0.034 * a) / (b * r) * a ^ 2 := by
        field_simp [bp.ne', dp.ne', rp.ne']
      _ = _ := by rw [prod]; field_simp [positive.ne']
  have area : (8 * π / 0.264384) * (1 - 0.034 * a) ≤ 95.064 * (1 - 0.034 * a) := by
    apply mul_le_mul_of_nonneg_right
    · apply (div_le_iff₀ (by norm_num)).mpr
      have pi_upper : π < 3.141593 := pi_lt_d6
      linarith only [pi_upper]
    · linarith only [amax]
  have charge : (2 * (J : ℝ) + 1 + 1.903 / a) * Δ / r * a ^ 2 ≤ 8.76 * a := by
    have weight : 0 ≤ (1 + 1.903 / a) * a ^ 2 := by positivity
    have upper := mul_le_mul_of_nonneg_left rel weight
    have eq : (1 + 1.903 / a) * a ^ 2 = a ^ 2 + 1.903 * a := by
      field_simp [positive.ne']
    have square_le : a ^ 2 ≤ 0.524 * a := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right amax positive.le
    have meridian : (J : ℝ) * Δ ≤ π := by
      rw [show (J : ℝ) * Δ = π - 2 * AcuteLatitudeGrid.polarRadius a from count_mul_step positive small]
      linarith only [AcuteLatitudeGrid.polarRadius_pos positive]
    have nominal : (2 * π) * a ^ 2 / r = (2 * π / 0.72) * (√a * a) := by
      have root : (√a) ^ 2 = a := sq_sqrt positive.le
      dsimp only [r, radius]
      field_simp [(sqrt_pos.mpr positive).ne']
      exact root.symm
    have pi_scaled : 2 * π / (0.72 : ℝ) ≤ 8.727 := by
      apply (div_le_iff₀ (by norm_num)).mpr
      have pi_upper : π < 3.141593 := pi_lt_d6
      linarith only [pi_upper]
    have meridional : (2 * π) * a ^ 2 / r ≤ 6.32 * a := by
      rw [nominal, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ positive.le
      calc
        _ ≤ 8.727 * 0.724 := mul_le_mul pi_scaled (radius_root_upper small).le
          (sqrt_nonneg _) (by norm_num)
        _ ≤ _ := by norm_num
    calc
      _ = (2 * ((J : ℝ) * Δ)) * a ^ 2 / r +
          ((1 + 1.903 / a) * a ^ 2) * Δ / r := by ring
      _ ≤ (2 * π) * a ^ 2 / r + (a ^ 2 + 1.903 * a) := by
        apply add_le_add
        · apply div_le_div_of_nonneg_right _ rp.le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left meridian (by norm_num)) ap.le
        · rw [← eq]
          exact (div_le_iff₀ rp).mpr upper
      _ ≤ _ := by linarith only [meridional, square_le, positive]
  apply (lt_div_iff₀ ap).mpr
  have count := mul_lt_mul_of_pos_right
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right
      (triangleCount_lt_rows positive small) dp) rp) ap
  have distributing :
      (2 * (J : ℝ) + 1 + 1.903 / a + 8 * π * (1 - 0.034 * a) / (b * Δ)) * Δ / r * a ^ 2 =
        (2 * (J : ℝ) + 1 + 1.903 / a) * Δ / r * a ^ 2 +
          (8 * π * (1 - 0.034 * a) / (b * Δ) * Δ / r * a ^ 2) := by ring
  rw [distributing, pure] at count
  linarith only [count, area, charge, amax]

private theorem stripCount_mul_radius_lt (positive : 0 < a) (small : a ≤ π / 6) :
    (stripCount a : ℝ) * radius a < π - 2 * AcuteLatitudeGrid.polarRadius a + radius a := by
  have rp := radius_pos positive
  have meridian : 0 ≤ π - 2 * AcuteLatitudeGrid.polarRadius a := by
    linarith only [pi_gt_d2, AcuteLatitudeGrid.polarRadius_lt small]
  have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg meridian rp.le)) rp
  rw [add_mul, div_mul_cancel₀ _ rp.ne', one_mul] at h
  exact h

/-- Without the meridional weight, rounding the number of strips is significant.
Splitting at six strips keeps the total base-angle charge within the bound. -/
theorem triangleCount_mul_cube_lt (positive : 0 < a) (small : a ≤ π / 6) :
    (triangleCount a : ℝ) * a ^ 3 < 55.9 := by
  let r := radius a
  let b := spacing a
  let Δ := rowStep a
  let J := stripCount a
  let m := π - 2 * AcuteLatitudeGrid.polarRadius a
  have rp : 0 < r := radius_pos positive
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < Δ := rowStep_pos positive small
  have jp : 0 < (J : ℝ) := Nat.cast_pos.mpr (stripCount_pos positive small)
  have ap := pow_pos positive 3
  have mp : 3.0195 < m := by
    have lower : 3.1415 < π := pi_gt_d4
    dsimp only [m]
    linarith only [lower, AcuteLatitudeGrid.polarRadius_lt small]
  have am : a ≤ 0.524 := by
    have pi_upper : π < 3.141593 := pi_lt_d6
    linarith only [small, pi_upper]
  have rm : r ≤ 0.72 * 0.724 := by
    dsimp only [r, radius]
    exact mul_le_mul_of_nonneg_left (radius_root_upper small).le (by norm_num)
  have meridian : (J : ℝ) * Δ = m := count_mul_step positive small
  have corners := mul_lt_mul_of_pos_right (triangleCount_lt_rows positive small) ap
  have prod : b * r = 0.264384 * a ^ 2 := scale_product positive
  have normalize : 8 * π * (1 - 0.034 * a) / (b * Δ) * a ^ 3 =
      (8 * π / 0.264384) * ((a * (1 - 0.034 * a)) * (r / Δ)) := by
    calc
      _ = (8 * π / (b * r)) * ((a ^ 3 * (1 - 0.034 * a)) * (r / Δ)) := by
        field_simp [bp.ne', rp.ne', dp.ne']
      _ = _ := by rw [prod]; field_simp [positive.ne', dp.ne']
  have distribute :
      (2 * (J : ℝ) + 1 + 1.903 / a + 8 * π * (1 - 0.034 * a) / (b * Δ)) * a ^ 3 =
        (2 * (J : ℝ) + 1) * a ^ 3 + 1.903 * a ^ 2 +
          8 * π * (1 - 0.034 * a) / (b * Δ) * a ^ 3 := by
    field_simp [positive.ne', bp.ne', dp.ne']
  rw [distribute, normalize] at corners
  have factor : 8 * π / (0.264384 : ℝ) ≤ 95.064 := by
    apply (div_le_iff₀ (by norm_num)).mpr
    have pi_upper : π < 3.141593 := pi_lt_d6
    linarith only [pi_upper]
  have nonnegative : 0 ≤ a * (1 - 0.034 * a) := by
    apply mul_nonneg positive.le
    linarith only [am]
  by_cases few : J ≤ 6
  · have cast : (J : ℝ) ≤ 6 := by exact_mod_cast few
    have cap : (a * (1 - 0.034 * a)) * (r / Δ) ≤ 0.543 := by
      have numerator : a * r * J ≤ (0.524 * (0.72 * 0.724)) * 6 := by
        exact mul_le_mul (mul_le_mul am rm rp.le (by norm_num)) cast jp.le (by norm_num)
      calc
        _ ≤ a * (r / Δ) := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg a])
          (div_nonneg rp.le dp.le)
        _ = a * r * J / m := by rw [← meridian]; field_simp [dp.ne', jp.ne']
        _ ≤ _ := by
          apply (div_le_iff₀ (by linarith only [mp])).mpr
          linarith only [numerator, mp]
    have charge := mul_le_mul factor cap (mul_nonneg nonnegative (div_nonneg rp.le dp.le))
      (show (0 : ℝ) ≤ 95.064 by norm_num)
    have cubes := pow_le_pow_left₀ positive.le am 3
    have squares := pow_le_pow_left₀ positive.le am 2
    have row := mul_le_mul (show 2 * (J : ℝ) + 1 ≤ 13 by linarith only [cast])
      cubes ap.le (show (0 : ℝ) ≤ 13 by norm_num)
    linarith only [corners, row, squares, charge]
  · have many : (7 : ℝ) ≤ J := by
      have h : 7 ≤ J := by omega
      exact_mod_cast h
    have upper : (J : ℝ) * r < m + r := stripCount_mul_radius_lt positive small
    have ar : a < 0.4907 := by
      have six : 6 * r < m := by
        have h := mul_le_mul_of_nonneg_right many rp.le
        linarith only [h, upper]
      have root : √a < 22 / 7 / (6 * (0.72 : ℝ) + 1 / 6) := by
        change 6 * (0.72 * √a) < π - 2 * (√a / 12) at six
        apply (lt_div_iff₀ (by norm_num)).mpr
        have pi_upper : π < 22 / 7 := by
          have h : π < 3.141593 := pi_lt_d6
          linarith only [h]
        linarith only [six, pi_upper]
      have sq := pow_lt_pow_left₀ root (sqrt_nonneg a) (by decide : 2 ≠ 0)
      rw [sq_sqrt positive.le] at sq
      norm_num at sq ⊢
      linarith only [sq]
    have ratio : r / Δ ≤ 7 / 6 := by
      apply (div_le_iff₀ dp).mpr
      have bound : (J : ℝ) * Δ ≤ (7 / 6) * ((J : ℝ) - 1) * Δ :=
        mul_le_mul_of_nonneg_right (by linarith only [many]) dp.le
      have h : ((J : ℝ) - 1) * r < (J : ℝ) * Δ := by
        rw [meridian]
        linarith only [upper]
      apply (mul_le_mul_iff_of_pos_left (show 0 < (J : ℝ) - 1 by linarith only [many])).mp
      nlinarith only [h, bound]
    have a_comp : a * (1 - 0.034 * a) ≤ 0.4907 * (1 - 0.034 * 0.4907) := by
      have h := mul_nonneg (sub_nonneg.mpr ar.le)
        (show 0 ≤ 1 - 0.034 * (a + 0.4907) by linarith only [am])
      nlinarith only [h]
    have cap : (a * (1 - 0.034 * a)) * (r / Δ) ≤ 0.563 := by
      exact (mul_le_mul a_comp ratio (div_nonneg rp.le dp.le) (by norm_num)).trans (by norm_num)
    have charge := mul_le_mul factor cap (mul_nonneg nonnegative (div_nonneg rp.le dp.le))
      (show (0 : ℝ) ≤ 95.064 by norm_num)
    have fewer : (J : ℝ) ≤ π / r + 1 := by
      have h := (le_div_iff₀ rp).mpr
        (show ((J : ℝ) - 1) * r ≤ π from by
          dsimp only [m] at upper
          linarith only [upper, (AcuteLatitudeGrid.polarRadius_pos positive).le])
      linarith only [h]
    have normalize_row : (2 * (π / r + 1) + 1) * a ^ 3 =
        (2 * π / 0.72) * (a ^ 2 * √a) + 3 * a ^ 3 := by
      dsimp only [r, radius]
      field_simp [(sqrt_pos.mpr positive).ne']
      linear_combination -(2 * π) * (sq_sqrt positive.le)
    have root_bound : √a ≤ 0.701 := by
      apply (sqrt_le_iff).mpr
      exact ⟨by norm_num, by linarith only [ar]⟩
    have cubes := pow_le_pow_left₀ positive.le ar.le 3
    have squares := pow_le_pow_left₀ positive.le ar.le 2
    have pi_scaled : 2 * π / (0.72 : ℝ) ≤ 8.727 := by
      apply (div_le_iff₀ (by norm_num)).mpr
      have pi_upper : π < 3.141593 := pi_lt_d6
      linarith only [pi_upper]
    have row := mul_le_mul_of_nonneg_right
      (show 2 * (J : ℝ) + 1 ≤ 2 * (π / r + 1) + 1 by linarith only [fewer]) ap.le
    rw [normalize_row] at row
    have rem := mul_le_mul pi_scaled
      (mul_le_mul squares root_bound (sqrt_nonneg _) (by norm_num))
      (show 0 ≤ a ^ 2 * √a by positivity) (by norm_num)
    linarith only [corners, row, cubes, squares, charge, rem]

end Unfoldings.FewestNets.RevisedLatitudeGrid
