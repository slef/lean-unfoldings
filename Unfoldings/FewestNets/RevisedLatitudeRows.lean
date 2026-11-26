module

public import Unfoldings.FewestNets.AcuteLatitudeMetricRows
public import Unfoldings.FewestNets.AcutePolarScalars

/-! The taller latitude bands and denser polar rings of the revised grid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The revised target meridional length. -/
def radius (a : ℝ) : ℝ := 0.72 * √a

/-- The nonpolar target row interval. -/
def spacing (a : ℝ) : ℝ := 0.51 * a * radius a

/-- The two refinements at a polar row are the smaller spacing and minimum count. -/
def polarSize (a : ℝ) : ℕ :=
  max 6 ⌈2 * π * sin (AcuteLatitudeGrid.polarRadius a) / (0.6 * spacing a)⌉₊

/-- The number of bands between the two polar rows. -/
def stripCount (a : ℝ) : ℕ := ⌈(π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a⌉₊

/-- The exact meridional separation of two adjacent rows. -/
def rowStep (a : ℝ) : ℝ := (π - 2 * AcuteLatitudeGrid.polarRadius a) / (stripCount a : ℝ)

/-- Latitude ring centers in the spherical colatitude coordinate. -/
def colatitude (a : ℝ) (j : ℕ) : ℝ := AcuteLatitudeGrid.polarRadius a + j * rowStep a

/-- Interior rows use the original midpoint sampling rule at the revised scale. -/
def rowSize (a : ℝ) (j : ℕ) : ℕ :=
  if j = 0 ∨ j = stripCount a then polarSize a else ⌈2 * π * sin (colatitude a j) / spacing a⌉₊

variable {a : ℝ}

theorem radius_pos (positive : 0 < a) : 0 < radius a :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr positive)

theorem spacing_pos (positive : 0 < a) : 0 < spacing a :=
  mul_pos (mul_pos (by norm_num) positive) (radius_pos positive)

theorem radius_lt (small : a ≤ π / 6) : radius a < 0.522 := by
  have square : a < (0.725 : ℝ) ^ 2 := by linarith only [small, pi_lt_d6]
  have root := Real.sqrt_lt' (show (0 : ℝ) < 0.725 by norm_num) |>.mpr square
  unfold radius
  linarith only [root]

private theorem meridian_pos (small : a ≤ π / 6) : 0 < π - 2 * AcuteLatitudeGrid.polarRadius a := by
  linarith only [AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2]

theorem stripCount_pos (positive : 0 < a) (small : a ≤ π / 6) : 0 < stripCount a :=
  Nat.one_le_ceil_iff.mpr (div_pos (meridian_pos small) (radius_pos positive))

theorem rowStep_bounds (positive : 0 < a) (small : a ≤ π / 6) :
    0.852 * radius a < rowStep a ∧ rowStep a ≤ radius a := by
  have rp := radius_pos positive
  have denominator : 0 < (stripCount a : ℝ) := Nat.cast_pos.mpr (stripCount_pos positive small)
  have floor := (div_le_iff₀ rp).mp
    (Nat.le_ceil ((π - 2 * AcuteLatitudeGrid.polarRadius a) / radius a))
  have upper := Nat.ceil_lt_add_one (div_nonneg (meridian_pos small).le rp.le)
  change (stripCount a : ℝ) < _ at upper
  have scaled := mul_lt_mul_of_pos_right upper rp
  rw [add_mul, div_mul_cancel₀ _ rp.ne', one_mul] at scaled
  have margin : 0.852 * radius a < 0.148 * (π - 2 * AcuteLatitudeGrid.polarRadius a) := by
    linarith only [radius_lt small, AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2]
  unfold rowStep
  exact ⟨(lt_div_iff₀ denominator).mpr (by nlinarith only [margin, scaled]),
    (div_le_iff₀ denominator).mpr (by
      rw [mul_comm (radius a)]
      exact floor)⟩

theorem colatitude_last (positive : 0 < a) (small : a ≤ π / 6) :
    colatitude a (stripCount a) = π - AcuteLatitudeGrid.polarRadius a := by
  unfold colatitude rowStep
  rw [mul_comm (stripCount a : ℝ), div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (stripCount_pos positive small).ne')]
  ring

/-- The refined polar row is symmetric between the two hemispheres. -/
theorem rowSize_at_poles : rowSize a 0 = polarSize a ∧ rowSize a (stripCount a) = polarSize a := by
  simp [rowSize]

private theorem spacing_eq_polar (a : ℝ) : spacing a = 4.4064 * a * AcuteLatitudeGrid.polarRadius a := by
  unfold spacing radius AcuteLatitudeGrid.polarRadius
  ring

/-- The revised polar rings have enough sides for the polar development and
remain small enough for the new component count. -/
theorem polarSize_bounds (positive : 0 < a) (small : a ≤ π / 6) :
    6 ≤ polarSize a ∧ (polarSize a : ℝ) < 3.15 / a ∧ π / (polarSize a : ℝ) < 1.33 * a := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  let q := 2 * π * sin ρ / (0.6 * spacing a)
  let k := polarSize a
  have rad : 0 < ρ := AcuteLatitudeGrid.polarRadius_pos positive
  have rad_lt : ρ < 0.061 := AcuteLatitudeGrid.polarRadius_lt small
  have sine_low : 0.999 * ρ < sin ρ := by
    have square : ρ ^ 2 < (0.061 : ℝ) ^ 2 := pow_lt_pow_left₀ rad_lt rad.le (by decide)
    have cubic := mul_lt_mul_of_pos_left square rad
    have error : ρ ^ 3 / 6 < 0.001 * ρ := by
      calc
        ρ ^ 3 / 6 = ρ * ρ ^ 2 / 6 := by ring
        _ < ρ * (0.061 : ℝ) ^ 2 / 6 := div_lt_div_of_pos_right cubic (by norm_num)
        _ ≤ 0.001 * ρ := by
          rw [mul_div_assoc, mul_comm 0.001]
          exact mul_le_mul_of_nonneg_left (by norm_num) rad.le
    linarith only [sin_gt_sub_cube rad, error]
  have sine_high : sin ρ ≤ ρ := Real.sin_le rad.le
  have hden : 0 < 0.6 * spacing a := mul_pos (by norm_num) (spacing_pos positive)
  have qpos : 0 < q := div_pos (mul_pos (mul_pos (by norm_num) pi_pos)
    ((mul_pos (by norm_num) rad).trans sine_low)) hden
  have lower : 6 ≤ k := le_max_left _ _
  have kpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have upperQ : q * a ≤ 2 * π / 2.64384 := by
    calc
      _ ≤ (2 * π * ρ / (0.6 * spacing a)) * a :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left sine_high (by positivity)) hden.le) positive.le
      _ = _ := by
        rw [spacing_eq_polar]
        change (2 * π * ρ / (0.6 * (4.4064 * a * ρ))) * a = _
        field_simp [rad.ne', positive.ne'] <;> ring
  have q_le : q ≤ (k : ℝ) := (Nat.le_ceil q).trans (by exact_mod_cast le_max_right 6 ⌈q⌉₊)
  have upper_count : (k : ℝ) * a < 3.15 := by
    change (max 6 ⌈q⌉₊ : ℕ) * (a : ℝ) < 3.15
    rw [Nat.cast_max, max_mul_of_nonneg _ _ positive.le]
    apply max_lt
    · norm_num
      linarith only [small, pi_lt_d6]
    · have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one qpos.le) positive
      rw [add_mul, one_mul] at h
      have scaled : 2 * π / (2.64384 : ℝ) < 2.4 := by
        apply (div_lt_iff₀ (by norm_num)).mpr
        linarith only [Real.pi_lt_d6]
      have a_lt : a < 0.525 := by linarith only [small, Real.pi_lt_d6]
      linarith only [h, upperQ, scaled, a_lt]
  have lower_count : π < (1.33 * a) * (k : ℝ) := by
    calc
      π < (1.33 * a) * q := by
        rw [show (1.33 * a) * q = (1.33 * a * (2 * π * sin ρ)) / (0.6 * spacing a) by
          dsimp only [q]; ring]
        apply (lt_div_iff₀ hden).mpr
        rw [spacing_eq_polar]
        have h := mul_lt_mul_of_pos_left sine_low (mul_pos (mul_pos (by norm_num : 0 < (2.66 : ℝ))
          positive) pi_pos)
        change π * (0.6 * (4.4064 * a * ρ)) < _
        nlinarith only [h, show 0 < a * π * ρ from by positivity]
      _ ≤ (1.33 * a) * (k : ℝ) := mul_le_mul_of_nonneg_left q_le (by positivity)
  exact ⟨lower, (lt_div_iff₀ positive).mpr upper_count, (div_lt_iff₀ kpos).mpr lower_count⟩

theorem rowStep_pos (positive : 0 < a) (small : a ≤ π / 6) : 0 < rowStep a :=
  (mul_pos (by norm_num) (radius_pos positive)).trans (rowStep_bounds positive small).1

theorem colatitude_succ (j : ℕ) : colatitude a (j + 1) = colatitude a j + rowStep a := by
  simp only [colatitude, Nat.cast_add, Nat.cast_one]
  ring

theorem colatitude_bounds (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) :
    colatitude a j ∈ Set.Icc (AcuteLatitudeGrid.polarRadius a)
      (π - AcuteLatitudeGrid.polarRadius a) := by
  have monotone : Monotone (colatitude a) := fun x y xy =>
    add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr xy)
      (rowStep_pos positive small).le) _
  exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) (rowStep_pos positive small).le),
    (monotone valid).trans_eq (colatitude_last positive small)⟩

theorem colatitude_mem (positive : 0 < a) (small : a ≤ π / 6) {j : ℕ}
    (valid : j ≤ stripCount a) : colatitude a j ∈ Set.Ioo 0 π := by
  obtain ⟨low, high⟩ := colatitude_bounds positive small valid
  have hp := AcuteLatitudeGrid.polarRadius_pos positive
  exact ⟨hp.trans_le low, high.trans_lt (by linarith only [hp])⟩

/-- The polar ring's sine is estimated more closely for both the angular mesh
and the two polar-row contributions to the count. -/
theorem polar_sin_sharp (positive : 0 < a) (small : a ≤ π / 6) :
    0.99937 * AcuteLatitudeGrid.polarRadius a < sin (AcuteLatitudeGrid.polarRadius a) := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  have rad := AcuteLatitudeGrid.polarRadius_pos positive
  have rad_lt := AcuteLatitudeGrid.polarRadius_lt small
  have square : ρ ^ 2 ≤ (0.061 : ℝ) ^ 2 := pow_le_pow_left₀ rad.le rad_lt.le 2
  have error : ρ ^ 3 / 6 ≤ 0.00063 * ρ := by
    calc
      _ = (ρ ^ 2 / 6) * ρ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [square]) rad.le
  change 0.99937 * ρ < sin ρ
  linarith only [sin_gt_sub_cube rad, error]

/-- The unrounded count for a polar row before the ring refinement. -/
def polarSampling (a : ℝ) : ℝ :=
  2 * π * sin (AcuteLatitudeGrid.polarRadius a) / spacing a

theorem polarSampling_bounds (positive : 0 < a) (small : a ≤ π / 6) :
    2.72 < polarSampling a ∧ polarSampling a * a < 1.42725 := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  let q := polarSampling a
  have rad : 0 < ρ := AcuteLatitudeGrid.polarRadius_pos positive

  have qscaled : q * a = 2 * π * sin ρ / (4.4064 * ρ) := by
    change 2 * π * sin ρ / spacing a * a = _
    rw [spacing_eq_polar]
    change 2 * π * sin ρ / (4.4064 * a * ρ) * a = _
    field_simp [rad.ne', positive.ne']
  have den : 0 < 4.4064 * ρ := by positivity
  have qlo : 0.99937 * (2 * π / 4.4064) < q * a := by
    rw [qscaled]
    apply (lt_div_iff₀ den).mpr
    calc
      _ = (2 * π) * (0.99937 * ρ) := by ring
      _ < _ := mul_lt_mul_of_pos_left (polar_sin_sharp positive small) (by positivity)
  have qhi : q * a ≤ 2 * π / 4.4064 := by
    rw [qscaled]
    apply (div_le_iff₀ den).mpr
    calc
      _ ≤ (2 * π) * ρ := mul_le_mul_of_nonneg_left (sin_le rad.le) (by positivity)
      _ = _ := by ring
  constructor
  · apply (mul_lt_mul_iff_of_pos_right positive).mp
    calc
      2.72 * a ≤ (2.72 / 6) * π := by
        linarith only [small]
      _ < (0.99937 * (2 / 4.4064)) * π := by
        exact mul_lt_mul_of_pos_right (by norm_num) pi_pos
      _ = 0.99937 * (2 * π / 4.4064) := by ring
      _ < q * a := qlo
  · apply qhi.trans_lt
    apply (div_lt_iff₀ (by norm_num)).mpr
    have pi_upper : π < 3.141593 := pi_lt_d6
    linarith only [pi_upper]

/-- The polar refinement's ceiling and minimum count share this upper bound. -/
theorem polarSize_lt_sampling (positive : 0 < a) (small : a ≤ π / 6) :
    (polarSize a : ℝ) < (5 / 3 : ℝ) * polarSampling a + 1.5 := by
  have q := (polarSampling_bounds positive small).1
  unfold polarSize
  rw [Nat.cast_max, Nat.cast_ofNat]
  apply max_lt
  · linarith only [q]
  · have same : 2 * π * sin (AcuteLatitudeGrid.polarRadius a) / (0.6 * spacing a) =
      (5 / 3 : ℝ) * polarSampling a := by
      unfold polarSampling
      ring
    rw [same]
    have nonnegative : 0 ≤ (5 / 3 : ℝ) * polarSampling a := by linarith only [q]
    linarith only [Nat.ceil_lt_add_one nonnegative]

end Unfoldings.FewestNets.RevisedLatitudeGrid
