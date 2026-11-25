module

public import Unfoldings.Geometry.SharpDevelopmentThreshold
public import Unfoldings.Roof.SharpAngleProjection

/-! Tilt and heading margins at the three-exit selector parameters. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The sharp projection allowance is at most the square of a small tilt. -/
theorem projection_allowance_le_sq {φ : ℝ} (nonneg : 0 ≤ φ) (small : φ ≤ 1 / 10) :
    2 * arcsin ((1 - cos φ) / (1 + cos φ)) ≤ φ ^ 2 := by
  have square : φ ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ nonneg small _
  have cos_lower : (1 : ℝ) / 2 ≤ cos φ :=
    (by linarith only [square] : (1 : ℝ) / 2 ≤ 1 - φ ^ 2 / 2).trans one_sub_sq_div_two_le_cos
  have den_pos : 0 < 1 + cos φ := by linarith
  have ratio_nonneg : 0 ≤ (1 - cos φ) / (1 + cos φ) :=
    div_nonneg (sub_nonneg.mpr (cos_le_one φ)) den_pos.le
  have ratio : (1 - cos φ) / (1 + cos φ) ≤ φ ^ 2 / 3 := by
    apply (div_le_iff₀ den_pos).mpr
    have prod := mul_le_mul_of_nonneg_left cos_lower (show 0 ≤ φ ^ 2 / 3 by positivity)
    linarith only [one_sub_sq_div_two_le_cos (x := φ), prod]
  let t := φ ^ 2 / 2
  have t_nonneg : 0 ≤ t := by dsimp [t]; positivity
  have t_small : t ≤ 1 := by dsimp [t]; linarith only [square]
  have sq := pow_le_pow_left₀ t_nonneg t_small 2
  have cube := mul_le_mul_of_nonneg_left sq t_nonneg
  have sine_lower : φ ^ 2 / 3 ≤ sin t := by
    have sin_estimate := sin_ge_sub_cube t_nonneg
    have cube_le : t ^ 3 ≤ t := by nlinarith only [cube]
    have linear : φ ^ 2 / 3 = 2 * t / 3 := by dsimp [t]; ring
    rw [linear]
    linarith only [sin_estimate, cube_le, t_nonneg]
  have arcsine := (arcsin_le_iff_le_sin
    ⟨by linarith only [ratio_nonneg], (ratio.trans sine_lower).trans (sin_le_one t)⟩
    ⟨by linarith only [t_nonneg, pi_pos], by linarith only [t_small, pi_gt_three]⟩).mpr
    (ratio.trans sine_lower)
  dsimp [t] at arcsine
  linarith only [arcsine]

/-- At the latitude grid's tilt scale the projected input remains below the
heading cutoff `π / 2 - a / 8`, and the radial margin permits development. -/
theorem three_exit_tilt_bounds {a φ : ℝ} (positive : 0 < a) (small : a ≤ 1 / 10)
    (tilt_nonneg : 0 ≤ φ) (tilt_bound : φ ^ 2 ≤ a / 100000) :
    0 < cos φ ∧
      π / 2 - a + 2 * arcsin ((1 - cos φ) / (1 + cos φ)) < π / 2 - a / 8 ∧
      0 < sin (a / 32) ∧ sin (a / 32) < 1 ∧ φ ≤ √(sin (a / 32)) / 10 := by
  have tilt_small : φ ≤ 1 / 10 := by
    by_contra! above
    have sq := pow_lt_pow_left₀ above (by norm_num : 0 ≤ (1 : ℝ) / 10) (by decide : (2 : ℕ) ≠ 0)
    linarith only [sq, tilt_bound, small]
  have cos_pos : 0 < cos φ :=
    cos_pos_of_mem_Ioo ⟨by linarith only [tilt_nonneg, pi_pos], by
      linarith only [tilt_small, pi_gt_three]⟩
  have allowance := projection_allowance_le_sq tilt_nonneg tilt_small
  have a32_pos : 0 < a / 32 := div_pos positive (by norm_num)
  have a32_small : a / 32 ≤ 1 := by linarith only [small]
  have power := pow_le_pow_left₀ a32_pos.le a32_small 2
  have cube := mul_le_mul_of_nonneg_left power a32_pos.le
  have sine_lower : a / 64 ≤ sin (a / 32) := by
    have cube_le : (a / 32) ^ 3 ≤ a / 32 := by nlinarith only [cube]
    linarith only [cube_le, sin_ge_sub_cube a32_pos.le, a32_pos]
  have sine_pos : 0 < sin (a / 32) := (by linarith only [positive] : 0 < a / 64).trans_le sine_lower
  have sine_lt : sin (a / 32) < 1 := (Real.sin_le a32_pos.le).trans_lt (by linarith only [small])
  have square_bound : φ ^ 2 ≤ sin (a / 32) / 100 := by
    linarith only [positive, tilt_bound, sine_lower]
  refine ⟨cos_pos, by linarith only [allowance, tilt_bound, positive], sine_pos, sine_lt, ?_⟩
  by_contra! above
  have sq := pow_lt_pow_left₀ above (by positivity : 0 ≤ √(sin (a / 32)) / 10)
    (by decide : (2 : ℕ) ≠ 0)
  rw [div_pow, sq_sqrt sine_pos.le] at sq
  norm_num at sq
  exact sq.not_ge square_bound

end Unfoldings.FewestNets
