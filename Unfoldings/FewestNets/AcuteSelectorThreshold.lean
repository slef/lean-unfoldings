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

/-- The current latitude grid has enough tilt clearance for both the
projected input angle bound and the acute-cone development threshold. -/
theorem latitude_three_exit_tilt_bounds {a φ : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (tilt_nonneg : 0 ≤ φ) (tilt_bound : φ ≤ 0.0848 * √a) :
    0 < cos φ ∧
      π / 2 - a + 2 * arcsin ((1 - cos φ) / (1 + cos φ)) < π / 2 - 0.99 * a ∧
      0.234 * a < sin (0.235 * a) ∧ sin (0.235 * a) ≤ 1 / 5 ∧
      φ ^ 2 ≤ sin (0.235 * a) / 32 := by
  have a_le : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have square := pow_le_pow_left₀ tilt_nonneg tilt_bound 2
  rw [mul_pow, sq_sqrt positive.le] at square
  have φ_small : φ ≤ 0.1 := by
    by_contra! above
    have lower := pow_lt_pow_left₀ above (by norm_num : (0 : ℝ) ≤ 0.1)
      (by decide : (2 : ℕ) ≠ 0)
    linarith only [lower, square, a_le]
  have cos_pos : 0 < cos φ := cos_pos_of_mem_Ioo
    ⟨by linarith only [tilt_nonneg, pi_pos], by linarith only [φ_small, pi_gt_three]⟩
  have allowance := projection_allowance_le_sq tilt_nonneg (by linarith only [φ_small])
  have angle : π / 2 - a + 2 * arcsin ((1 - cos φ) / (1 + cos φ)) <
      π / 2 - 0.99 * a := by linarith only [allowance, square, positive]
  let σ := (0.235 : ℝ) * a
  have σ_pos : 0 < σ := by dsimp [σ]; positivity
  have σ_small : σ ≤ 0.124 := by dsimp [σ]; linarith only [a_le]
  have σ_sq := pow_le_pow_left₀ σ_pos.le σ_small 2
  have σ_cube := mul_le_mul_of_nonneg_left σ_sq σ_pos.le
  have sine : 0.234 * a < sin σ := by
    have bound := sin_ge_sub_cube σ_pos.le
    have cube : σ ^ 3 ≤ (0.124 : ℝ) ^ 2 * σ := by nlinarith only [σ_cube]
    linarith only [bound, cube, show σ = 0.235 * a from rfl, positive]
  have sine_upper : sin σ ≤ 1 / 5 := (Real.sin_le σ_pos.le).trans
    (by linarith only [σ_small])
  refine ⟨cos_pos, angle, sine, sine_upper, ?_⟩
  change φ ^ 2 ≤ sin σ / 32
  linarith only [square, sine, positive]

/-- The gnomonic long-side estimates imply the strict shifted-window margins. -/
theorem latitude_three_exit_heading_margins {a e w : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (east : |e| ≤ 0.486 * a) (west : |w| ≤ 0.486 * a)
    (difference : w - e ≤ 0.49 * a) :
    let δ := (0.495 : ℝ) * a
    let σ := (0.235 : ℝ) * a
    0 < σ ∧ σ ≤ δ ∧ δ ≤ π / 8 ∧ |e| < 2 * δ ∧ |w| < 2 * δ ∧
      σ < δ + e / 2 ∧ σ < δ - w / 2 ∧ σ < 2 * δ + e - w := by
  have ep := (abs_le.mp east).1
  have wp := (abs_le.mp west).2
  dsimp only
  exact ⟨by positivity, by linarith only [positive], by linarith only [small, pi_pos],
    by linarith only [east, positive], by linarith only [west, positive],
    by linarith only [ep, positive], by linarith only [wp, positive],
    by linarith only [difference, positive]⟩

end Unfoldings.FewestNets
