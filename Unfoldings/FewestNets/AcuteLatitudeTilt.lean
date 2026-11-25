module

public import Unfoldings.FewestNets.AcuteLatitudeRows
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The revised tilt and angular-distortion constants for the latitude charts. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

/-- At the chart tilts of the acute latitude grid, the exact angular projection
distortion is at most `0.504 φ²`. -/
theorem acute_projection_allowance_le_sq {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ ≤ 0.134) :
    2 * arcsin ((1 - cos φ) / (1 + cos φ)) ≤ 0.504 * φ ^ 2 := by
  have square : φ ^ 2 ≤ (0.134 : ℝ) ^ 2 := pow_le_pow_left₀ nonnegative small 2
  have cosine := one_sub_sq_div_two_le_cos (x := φ)
  have den_lower : 1.991 ≤ 1 + cos φ := by linarith only [square, cosine]
  have den_pos : 0 < 1 + cos φ := by linarith only [den_lower]
  have ratio_nonneg : 0 ≤ (1 - cos φ) / (1 + cos φ) :=
    div_nonneg (sub_nonneg.mpr (cos_le_one φ)) den_pos.le
  have ratio : (1 - cos φ) / (1 + cos φ) ≤ 0.2512 * φ ^ 2 := by
    apply (div_le_iff₀ den_pos).mpr
    have product := mul_le_mul_of_nonneg_left den_lower (show 0 ≤ 0.2512 * φ ^ 2 by positivity)
    linarith only [cosine, product, sq_nonneg φ]
  let t := 0.252 * φ ^ 2
  have t_nonneg : 0 ≤ t := by dsimp [t]; positivity
  have t_small : t ≤ 0.005 := by dsimp [t]; linarith only [square]
  have sq := pow_le_pow_left₀ t_nonneg t_small 2
  have cube := mul_le_mul_of_nonneg_right sq t_nonneg
  have sine_lower : 0.2512 * φ ^ 2 ≤ sin t := by
    have remainder := abs_sub_sin_le t
    rw [abs_of_nonneg t_nonneg] at remainder
    nlinarith only [(abs_le.mp remainder).2, cube, sq_nonneg φ, show t = 0.252 * φ ^ 2 from rfl]
  have angle := (arcsin_le_iff_le_sin
    ⟨by linarith only [ratio_nonneg], (ratio.trans sine_lower).trans (sin_le_one t)⟩
    ⟨by linarith only [t_nonneg, pi_pos], by linarith only [t_small, pi_gt_three]⟩).mpr
    (ratio.trans sine_lower)
  dsimp [t] at angle
  linarith only [angle]

/-- The angular radius established by the chart shape proof leaves the
angle-distortion and curvature margins required by the revised construction. -/
theorem acute_latitude_tilt_budgets {a φ : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (nonnegative : 0 ≤ φ) (tilt : φ ≤ 0.568 * AcuteLatitudeGrid.radius a) :
    φ < 0.134 ∧ φ ^ 2 < 0.0335 * a ∧ 0 < cos φ ∧
      π / 2 - a + 2 * arcsin ((1 - cos φ) / (1 + cos φ)) < π / 2 - 0.982 * a := by
  have φ_small : φ < 0.134 := by
    linarith only [tilt, AcuteLatitudeGrid.radius_lt small]
  have sq := pow_le_pow_left₀ nonnegative tilt 2
  unfold AcuteLatitudeGrid.radius at sq
  rw [mul_pow, mul_pow, sq_sqrt positive.le] at sq
  have φ_sq : φ ^ 2 < 0.0335 * a := by linarith only [positive, sq]
  have cosine := cos_pos_of_mem_Ioo (x := φ)
    ⟨by linarith only [nonnegative, pi_pos], by linarith only [φ_small, pi_gt_three]⟩
  have allowance := acute_projection_allowance_le_sq nonnegative φ_small.le
  exact ⟨φ_small, φ_sq, cosine, by linarith only [φ_sq, allowance, positive]⟩

/-- The sum of the closing-path error and all bank rotations fits under the
new angular margin. -/
theorem acute_latitude_closing_budget {a φ Ω : ℝ} (positive : 0 < a)
    (nonnegative : 0 ≤ φ) (small : φ ≤ 0.134)
    (tilt : φ ^ 2 < 0.0335 * a) (curvature : Ω < 0.0163 * a) :
    4 * arcsin ((1 - cos φ) / (1 + cos φ)) + 2 * φ * sin φ + 4 * Ω < 0.170 * a := by
  have distortion := acute_projection_allowance_le_sq nonnegative small
  have closing := mul_le_mul_of_nonneg_left (sin_le nonnegative)
    (show 0 ≤ 2 * φ by positivity)
  nlinarith only [distortion, closing, tilt, curvature, positive]

end Unfoldings.FewestNets
