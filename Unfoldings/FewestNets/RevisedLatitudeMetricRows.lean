module

public import Unfoldings.FewestNets.RevisedLatitudeRows

/-! Metric controls on a sample's longitude, including the refined polar rows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

variable {a : ℝ}

/-- Angular length of one interval on the numbered row. -/
def longitudeStep (a : ℝ) (j : ℕ) : ℝ := 2 * π / rowSize a j

/-- Each refined polar interval has the smaller tangential length. -/
def localSpacing (a : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = stripCount a then 0.6 * spacing a else spacing a

theorem radius_eq_polarRadius (a : ℝ) : radius a = 8.64 * AcuteLatitudeGrid.polarRadius a := by
  unfold radius AcuteLatitudeGrid.polarRadius
  ring

theorem spacing_lt (positive : 0 < a) (small : a ≤ π / 6) : spacing a < 0.268 * radius a := by
  unfold spacing
  apply mul_lt_mul_of_pos_right _ (radius_pos positive)
  linarith only [small, pi_lt_d6]

private theorem sine_min_of_symmetric_interval {x y : ℝ} (low : 0 ≤ x)
    (range : y ∈ Set.Icc x (π - x)) : sin x ≤ sin y := by
  rcases le_or_gt y (π / 2) with below | above
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith only [low, pi_pos]) below range.1
  · rw [← sin_pi_sub y]
    apply sin_le_sin_of_le_of_le_pi_div_two (by linarith only [low, pi_pos])
    · linarith only [above]
    · linarith only [range.2]

/-- The circumference near the first interior row still controls its angular intervals. -/
theorem interior_sine_sharp (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (lower : 0 < j) (upper : j < stripCount a) :
    radius a < 1.0795 * sin (colatitude a j) := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  let r := radius a
  let d := rowStep a
  let x := ρ + 0.852 * r
  have dp := rowStep_pos positive small
  have step := (rowStep_bounds positive small).1
  have xp : 0 < x := add_pos (AcuteLatitudeGrid.polarRadius_pos positive)
    (mul_pos (by norm_num) (radius_pos positive))
  have xl : x < 0.506 := by
    dsimp only [x]
    linarith only [AcuteLatitudeGrid.polarRadius_lt small, radius_lt small]
  have r_eq : r = 8.64 * ρ := radius_eq_polarRadius a
  have x_eq : x = (1 / 8.64 + 0.852) * r := by
    dsimp only [x]
    linarith only [r_eq]
  have jlarge : (1 : ℝ) ≤ j := by exact_mod_cast lower
  have jbelow : (j : ℝ) + 1 ≤ (stripCount a : ℝ) := by exact_mod_cast upper
  have low_row : x ≤ colatitude a j := by
    have h := mul_le_mul_of_nonneg_right jlarge dp.le
    change ρ + 0.852 * r ≤ ρ + (j : ℝ) * d
    linarith only [h, step]
  have upper_row : colatitude a j ≤ π - x := by
    have h := mul_le_mul_of_nonneg_right jbelow dp.le
    have last := colatitude_last positive small
    change ρ + (stripCount a : ℝ) * d = π - ρ at last
    change ρ + (j : ℝ) * d ≤ π - (ρ + 0.852 * r)
    linarith only [h, last, step]
  have lower_sine := sine_min_of_symmetric_interval xp.le ⟨low_row, upper_row⟩
  have xsq := pow_le_pow_left₀ xp.le xl.le 2
  have error : x ^ 3 / 6 ≤ (0.506 : ℝ) ^ 2 / 6 * x := by
    rw [show x ^ 3 / 6 = (x ^ 2 / 6) * x by ring]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right xsq (by norm_num)) xp.le
  have sine : (1 - (0.506 : ℝ) ^ 2 / 6) * x < sin x := by
    linarith only [sin_gt_sub_cube xp, error]
  have calc_radius :
      r ≤ 1.0795 * ((1 - (0.506 : ℝ) ^ 2 / 6) * x) := by
    rw [x_eq, ← mul_assoc, ← mul_assoc]
    exact le_mul_of_one_le_left (radius_pos positive).le (by norm_num)
  exact calc_radius.trans_lt (mul_lt_mul_of_pos_left (sine.trans_le lower_sine) (by norm_num))


theorem interior_sine_bound (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (lower : 0 < j) (upper : j < stripCount a) :
    radius a < 1.080 * sin (colatitude a j) := by
  have sine := sin_pos_of_mem_Ioo (colatitude_mem positive small upper.le)
  exact (interior_sine_sharp positive small lower upper).trans
    (mul_lt_mul_of_pos_right (by norm_num) sine)

theorem polar_sine_bound (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (polar : j = 0 ∨ j = stripCount a) :
    radius a < 8.649 * sin (colatitude a j) := by
  have sine : sin (colatitude a j) = sin (AcuteLatitudeGrid.polarRadius a) := by
    rcases polar with rfl | rfl
    · simp [colatitude]
    · rw [colatitude_last positive small, sin_pi_sub]
  rw [sine, radius_eq_polarRadius]
  have h := mul_lt_mul_of_pos_left (polar_sin_sharp positive small)
    (show (0 : ℝ) < 8.649 by norm_num)
  linarith only [h, AcuteLatitudeGrid.polarRadius_pos positive]

theorem localSpacing_pos (positive : 0 < a) (j : ℕ) : 0 < localSpacing a j := by
  unfold localSpacing
  split
  · exact mul_pos (by norm_num) (spacing_pos positive)
  · exact spacing_pos positive

/-- Including the refinement, each row has at least its prescribed
unrounded sample count. -/
theorem sampling_le_rowSize (positive : 0 < a) (small : a ≤ π / 6) (j : ℕ) :
    2 * π * sin (colatitude a j) / localSpacing a j ≤ (rowSize a j : ℝ) := by
  by_cases polar : j = 0 ∨ j = stripCount a
  · rw [rowSize, localSpacing, ite_eq_left polar, ite_eq_left polar]
    have sine : sin (colatitude a j) = sin (AcuteLatitudeGrid.polarRadius a) := by
      rcases polar with rfl | h
      · simp [colatitude]
      · rw [h, colatitude_last positive small, sin_pi_sub]
    rw [sine, polarSize]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 6 _)
  · rw [rowSize, localSpacing, ite_eq_right polar, ite_eq_right polar]
    exact Nat.le_ceil _

theorem rowSize_ge_three (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) : 3 ≤ rowSize a j := by
  have sine := sine_min_of_symmetric_interval (AcuteLatitudeGrid.polarRadius_pos positive).le
    (colatitude_bounds positive small valid)
  have actual : polarSampling a ≤ (rowSize a j : ℝ) := by
    by_cases polar : j = 0 ∨ j = stripCount a
    · have p : localSpacing a j = 0.6 * spacing a := by rw [localSpacing, ite_eq_left polar]
      have denominator : localSpacing a j ≤ spacing a := by
        rw [p]
        exact mul_le_of_le_one_left (spacing_pos positive).le (by norm_num)
      have numer : 0 ≤ 2 * π * sin (colatitude a j) :=
        mul_nonneg (by positivity) (sin_pos_of_mem_Ioo (colatitude_mem positive small valid)).le
      calc
        _ ≤ 2 * π * sin (colatitude a j) / spacing a :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sine (by positivity))
            (spacing_pos positive).le
        _ ≤ 2 * π * sin (colatitude a j) / localSpacing a j :=
          div_le_div_of_nonneg_left numer (localSpacing_pos positive j) denominator
        _ ≤ _ := sampling_le_rowSize positive small j
    · have p : localSpacing a j = spacing a := by rw [localSpacing, ite_eq_right polar]
      calc
        _ ≤ 2 * π * sin (colatitude a j) / spacing a :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sine (by positivity))
            (spacing_pos positive).le
        _ ≤ _ := by simpa only [p] using sampling_le_rowSize positive small j
  have at_least : (2 : ℝ) < rowSize a j :=
    (show (2 : ℝ) < 2.72 by norm_num).trans ((polarSampling_bounds positive small).1.trans_le actual)
  exact Nat.succ_le_of_lt (Nat.cast_lt.mp at_least)

theorem rowSize_pos (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) : 0 < rowSize a j :=
  lt_of_lt_of_le (by decide) (rowSize_ge_three positive small valid)

theorem longitudeStep_pos_lt_pi (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) : 0 < longitudeStep a j ∧ longitudeStep a j < π := by
  have three : (3 : ℝ) ≤ (rowSize a j : ℝ) := by exact_mod_cast rowSize_ge_three positive small valid
  have count : 0 < (rowSize a j : ℝ) := by linarith only [three]
  unfold longitudeStep
  refine ⟨div_pos (by positivity) count, (div_lt_iff₀ count).mpr ?_⟩
  exact mul_lt_mul_of_pos_left (show (2 : ℝ) < rowSize a j by linarith only [three]) pi_pos
    |>.trans_eq' (mul_comm π 2)

/-- The midpoint rule controls the tangential distance to a row's nearest site. -/
theorem weighted_longitude_bound (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) {w : ℝ} (near : |w| ≤ longitudeStep a j / 2) :
    sin (colatitude a j) * |w| ≤ localSpacing a j / 2 := by
  have ks : 0 < (rowSize a j : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small valid)
  have sine := sin_pos_of_mem_Ioo (colatitude_mem positive small valid)
  have scale := (div_le_iff₀ (localSpacing_pos positive j)).mp (sampling_le_rowSize positive small j)
  calc
    _ ≤ sin (colatitude a j) * (longitudeStep a j / 2) :=
      mul_le_mul_of_nonneg_left near sine.le
    _ = (2 * π * sin (colatitude a j)) / (rowSize a j : ℝ) / 2 := by
      unfold longitudeStep
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply (div_le_iff₀ ks).mpr
      simpa only [mul_comm (localSpacing a j)] using scale

end Unfoldings.FewestNets.RevisedLatitudeGrid
