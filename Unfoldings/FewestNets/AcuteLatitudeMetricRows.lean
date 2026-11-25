module

public import Unfoldings.FewestNets.AcuteLatitudeRows

/-! Longitude spacing, weighted midpoint offsets, and polar side counts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- The angle between consecutive sites on one row. -/
def longitudeStep (a : ℝ) (j : ℕ) : ℝ := 2 * π / rowSize a j

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
theorem sin_polarRadius : 0.999 * polarRadius a < sin (polarRadius a) := by
  have hp := polarRadius_pos positive
  have square := pow_le_pow_left₀ hp.le (polarRadius_lt small).le 2
  have cube := mul_le_mul_of_nonneg_right square hp.le
  have remainder := abs_sub_sin_le (polarRadius a)
  rw [abs_of_pos hp] at remainder
  nlinarith only [(abs_le.mp remainder).2, cube, hp]

include positive small in
theorem sin_of_colatitude_bounds {x : ℝ} (hx : x ∈ Set.Icc (polarRadius a) (π - polarRadius a)) :
    0.999 * polarRadius a < sin x := by
  have left : -(π / 2) ≤ polarRadius a := by linarith [polarRadius_pos positive, pi_pos]
  apply (sin_polarRadius positive small).trans_le
  by_cases hx₀ : x ≤ π / 2
  · exact sin_le_sin_of_le_of_le_pi_div_two left hx₀ hx.1
  · rw [← sin_pi_sub x]
    exact sin_le_sin_of_le_of_le_pi_div_two left (by linarith only [hx₀])
      (by linarith only [hx.2])

include positive small in
theorem row_sine_lower {j : ℕ} (row : j ≤ stripCount a) :
    0.999 * polarRadius a < sin (colatitude a j) :=
  sin_of_colatitude_bounds positive small (colatitude_bounds positive small row)

include positive small in
theorem longitudeStep_bounds {j : ℕ} (row : j ≤ stripCount a) :
    spacing a / (1.182 * sin (colatitude a j)) < longitudeStep a j ∧
      longitudeStep a j ≤ spacing a / sin (colatitude a j) := by
  let s := sin (colatitude a j)
  let b := spacing a
  let k := rowSize a j
  have lower : 0.999 * polarRadius a < s := row_sine_lower positive small row
  have s_pos : 0 < s := by linarith only [polarRadius_pos positive, lower]
  have b_pos : 0 < b := spacing_pos positive
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small row)
  have ceil_low : 2 * π * s / b ≤ (k : ℝ) := Nat.le_ceil _
  have ceil_high : (k : ℝ) < 2 * π * s / b + 1 := Nat.ceil_lt_add_one (by positivity)
  have width := spacing_lt positive small
  rw [radius_eq_polarRadius] at width
  have b_circle : b < 0.182 * (2 * π * s) := by
    change b < _ at width
    have c := mul_lt_mul_of_pos_right pi_gt_d2 s_pos
    linarith only [width, lower, c, polarRadius_pos positive]
  have count : (k : ℝ) * b < 1.182 * s * (2 * π) := by
    have scaled := mul_lt_mul_of_pos_right ceil_high b_pos
    have cancel : (2 * π * s / b + 1) * b = 2 * π * s + b := by field_simp [b_pos.ne']
    rw [cancel] at scaled
    linarith only [scaled, b_circle]
  change b / (1.182 * s) < (2 * π) / k ∧ (2 * π) / k ≤ b / s
  constructor
  · exact (div_lt_div_iff₀ (mul_pos (by norm_num) s_pos) k_pos).mpr (by
      simpa only [mul_comm] using count)
  · exact (div_le_div_iff₀ k_pos s_pos).mpr (by
      simpa only [mul_comm] using (div_le_iff₀ b_pos).mp ceil_low)

include positive small in
/-- Consecutive sites have a positive longitude separation shorter than a half-turn. -/
theorem longitudeStep_pos_lt_pi {j : ℕ} (row : j ≤ stripCount a) :
    0 < longitudeStep a j ∧ longitudeStep a j < π := by
  have kp : 0 < (rowSize a j : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small row)
  have lower := row_sine_lower positive small row
  have sine_pos : 0 < sin (colatitude a j) := by linarith only [lower, polarRadius_pos positive]
  have upper := spacing_lt positive small
  rw [radius_eq_polarRadius] at upper
  have width : spacing a < 1.138 * sin (colatitude a j) := by
    linarith only [upper, lower, polarRadius_pos positive]
  refine ⟨div_pos (by positivity) kp, (longitudeStep_bounds positive small row).2.trans_lt ?_⟩
  exact ((div_lt_iff₀ sine_pos).mpr width).trans (by linarith only [pi_gt_d2])

include positive small in
/-- Each sweep site has a small longitude displacement in both row and midpoint units. -/
theorem weighted_longitude_bounds {j : ℕ} (row : j ≤ stripCount a) {ell w : ℝ}
    (latitude_gap : |ell - colatitude a j| ≤ radius a / 2)
    (offset : |w| ≤ longitudeStep a j / 2) :
    sin ell * |w| < 1.468 * spacing a ∧ sin (colatitude a j) * |w| ≤ spacing a / 2 := by
  let s := sin (colatitude a j)
  have lower : 0.999 * polarRadius a < s := row_sine_lower positive small row
  have s_pos : 0 < s := by linarith only [polarRadius_pos positive, lower]
  have spacing_bound : longitudeStep a j ≤ spacing a / s :=
    (longitudeStep_bounds positive small row).2
  have row_bound : s * |w| ≤ spacing a / 2 := by
    calc
      _ ≤ s * (spacing a / s / 2) := mul_le_mul_of_nonneg_left
        (offset.trans (div_le_div_of_nonneg_right spacing_bound (by norm_num))) s_pos.le
      _ = _ := by field_simp [s_pos.ne']
  have sine_difference : sin ell - s ≤ radius a / 2 :=
    (le_abs_self _).trans ((abs_sin_sub_sin_le ell (colatitude a j)).trans latitude_gap)
  rw [radius_eq_polarRadius] at sine_difference
  have sine_ratio : sin ell ≤ 2.935 * s := by
    linarith only [sine_difference, lower, polarRadius_pos positive]
  refine ⟨?_, row_bound⟩
  have first := mul_le_mul_of_nonneg_right sine_ratio (abs_nonneg w)
  have second := mul_le_mul_of_nonneg_left row_bound (by norm_num : (0 : ℝ) ≤ 2.935)
  linarith only [first, second, spacing_pos positive]

include positive small in
theorem first_last_row_size_eq : rowSize a 0 = rowSize a (stripCount a) := by
  unfold rowSize
  rw [colatitude_last positive small, sin_pi_sub]
  congr 3
  simp [colatitude]

include positive small in
/-- Both polar cells have the same number of sides and a short half-step. -/
theorem polar_size_bounds :
    let k := rowSize a 0
    6 ≤ k ∧ (k : ℝ) < 3.5 / a ∧ π / (k : ℝ) < 1.09 * a := by
  let k := rowSize a 0
  let ρ := polarRadius a
  let b := spacing a
  have kp : 0 < (k : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small (Nat.zero_le _))
  have ρp : 0 < ρ := polarRadius_pos positive
  have bp : 0 < b := spacing_pos positive
  have b_eq : b = 0.56 * 3.864 * a * ρ := by
    change 0.56 * a * radius a = _
    rw [radius_eq_polarRadius]
    ring
  have sine_lower : 0.999 * ρ < sin ρ := sin_polarRadius positive small
  have sine_upper := sin_le ρp.le
  have k_eq : k = ⌈2 * π * sin ρ / b⌉₊ := by simp [k, ρ, b, rowSize, colatitude]
  have ceil_low : 2 * π * sin ρ / b ≤ (k : ℝ) := by rw [k_eq]; exact Nat.le_ceil _
  have ceil_high : (k : ℝ) < 2 * π * sin ρ / b + 1 := by
    rw [k_eq]
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by positivity)
      (by linarith only [sine_lower, ρp])) bp.le)
  have lower : 0.999 * (2 * π) / (0.56 * 3.864) < (k : ℝ) * a := by
    have scaled := mul_lt_mul_of_pos_left sine_lower (show 0 < 2 * π by positivity)
    have product := (div_le_iff₀ bp).mp ceil_low
    rw [b_eq] at product
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 0.56 * 3.864)).mpr
    apply (mul_lt_mul_iff_of_pos_right ρp).mp
    nlinarith only [scaled, product]
  have upper : (k : ℝ) * a < 2 * π / (0.56 * 3.864) + a := by
    have scaled := mul_le_mul_of_nonneg_left sine_upper (show 0 ≤ 2 * π by positivity)
    have product := mul_lt_mul_of_pos_right ceil_high bp
    have cancel : (2 * π * sin ρ / b + 1) * b = 2 * π * sin ρ + b := by field_simp [bp.ne']
    rw [cancel, b_eq] at product
    apply (mul_lt_mul_iff_of_pos_right (show 0 < 0.56 * 3.864 * ρ by positivity)).mp
    have cancel' :
        (2 * π / (0.56 * 3.864) + a) * (0.56 * 3.864 * ρ) =
          2 * π * ρ + 0.56 * 3.864 * a * ρ := by ring
    rw [cancel']
    nlinarith only [product, scaled]
  have factor : 0 < (0.56 : ℝ) * 3.864 := by norm_num
  refine ⟨?_, (lt_div_iff₀ positive).mpr ?_, (div_lt_iff₀ kp).mpr ?_⟩
  · have estimate : 5 * a < 0.999 * (2 * π) / (0.56 * 3.864) :=
      (lt_div_iff₀ factor).mpr (by nlinarith only [small, pi_gt_d2, pi_lt_d4])
    have five : (5 : ℝ) < k :=
      (mul_lt_mul_iff_of_pos_right positive).mp (estimate.trans lower)
    have natural : 5 < k := by exact_mod_cast five
    omega
  · have ceiling : 2 * π / (0.56 * 3.864) < 2.91 :=
      (div_lt_iff₀ factor).mpr (by nlinarith only [pi_lt_d4])
    change (k : ℝ) * a < 3.5
    linarith only [small, pi_lt_d4, upper, ceiling]
  · have coefficient : π < 1.09 * (0.999 * (2 * π) / (0.56 * 3.864)) := by
      rw [← mul_div_assoc]
      exact (lt_div_iff₀ factor).mpr (by nlinarith only [pi_pos])
    exact coefficient.trans (by
      convert mul_lt_mul_of_pos_left lower (show (0 : ℝ) < 1.09 by norm_num) using 1
      ring)

end Unfoldings.FewestNets.AcuteLatitudeGrid
