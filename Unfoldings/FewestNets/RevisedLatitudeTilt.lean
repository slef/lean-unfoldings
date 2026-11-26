module

public import Unfoldings.FewestNets.RevisedLatitudeRows
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The angular distortion at the taller revised latitude bands. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

/-- At the chart tilts of the acute latitude grid, the exact angular projection
distortion is at most `0.512 φ²`. -/
theorem revised_projection_allowance_le_sq {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ ≤ 0.297) :
    2 * arcsin ((1 - cos φ) / (1 + cos φ)) ≤ 0.512 * φ ^ 2 := by
  have square : φ ^ 2 ≤ (0.297 : ℝ) ^ 2 := pow_le_pow_left₀ nonnegative small 2
  have cosine := one_sub_sq_div_two_le_cos (x := φ)
  have den_lower : 1.9558 ≤ 1 + cos φ := by linarith only [square, cosine]
  have den_pos : 0 < 1 + cos φ := by linarith only [den_lower]
  have ratio_nonneg : 0 ≤ (1 - cos φ) / (1 + cos φ) :=
    div_nonneg (sub_nonneg.mpr (cos_le_one φ)) den_pos.le
  have ratio : (1 - cos φ) / (1 + cos φ) ≤ 0.2557 * φ ^ 2 := by
    apply (div_le_iff₀ den_pos).mpr
    have product := mul_le_mul_of_nonneg_left den_lower (show 0 ≤ 0.2557 * φ ^ 2 by positivity)
    linarith only [cosine, product, sq_nonneg φ]
  let t := 0.256 * φ ^ 2
  have t_nonneg : 0 ≤ t := by dsimp [t]; positivity
  have t_small : t ≤ 0.0226 := by dsimp [t]; linarith only [square]
  have sq := pow_le_pow_left₀ t_nonneg t_small 2
  have cube := mul_le_mul_of_nonneg_right sq t_nonneg
  have sine_lower : 0.2557 * φ ^ 2 ≤ sin t := by
    have remainder := abs_sub_sin_le t
    rw [abs_of_nonneg t_nonneg] at remainder
    nlinarith only [(abs_le.mp remainder).2, cube, sq_nonneg φ, show t = 0.256 * φ ^ 2 from rfl]
  have angle := (arcsin_le_iff_le_sin
    ⟨by linarith only [ratio_nonneg], (ratio.trans sine_lower).trans (sin_le_one t)⟩
    ⟨by linarith only [t_nonneg, pi_pos], by linarith only [t_small, pi_gt_three]⟩).mpr
    (ratio.trans sine_lower)
  dsimp [t] at angle
  linarith only [angle]

end Unfoldings.FewestNets
