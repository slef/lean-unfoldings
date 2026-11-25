module

public import Unfoldings.Geometry.RadialBlockError
public import Unfoldings.Geometry.SharpDevelopmentMargin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.GCongr

/-! The paper's explicit square-root sufficient condition for the sharp development estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

/-- Total available Gaussian curvature for a roof of tilt at most `φ`. -/
def shallowDevelopmentCurvature (φ : ℝ) : ℝ := 2 * π * (1 - cos φ)

/-- Heading allowance including the local turn, crease, and opening contributions. -/
def shallowDevelopmentHeading (φ : ℝ) : ℝ :=
  3 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * π * ((cos φ)⁻¹ - 1) +
    6 * φ * sin φ + 2 * shallowDevelopmentCurvature φ

private theorem shallowDevelopment_sec_bounds {φ : ℝ} (φ_nonneg : 0 ≤ φ) (φ_small : φ ≤ 0.1) :
    1 ≤ (cos φ)⁻¹ ∧ (cos φ)⁻¹ ≤ 1.006 ∧ (cos φ)⁻¹ - 1 ≤ 0.503 * φ ^ 2 := by
  have φ_sq : φ ^ 2 ≤ (0.1 : ℝ) ^ 2 := pow_le_pow_left₀ φ_nonneg φ_small 2
  have cos_lower := one_sub_sq_div_two_le_cos (x := φ)
  have cos_numeric : 0.995 ≤ cos φ := by linarith only [φ_sq, cos_lower]
  have cos_pos : 0 < cos φ := by linarith only [cos_numeric]
  have inv_one : 1 ≤ (cos φ)⁻¹ := (one_le_inv₀ cos_pos).2 (cos_le_one φ)
  refine ⟨inv_one, ?_, ?_⟩
  · rw [← one_div]
    apply (div_le_iff₀ cos_pos).2
    linarith only [cos_numeric]
  · have difference : (cos φ)⁻¹ - 1 = (1 - cos φ) / cos φ := by
      field_simp [cos_pos.ne']
    rw [difference]
    apply (div_le_iff₀ cos_pos).2
    have scaled := mul_le_mul_of_nonneg_right cos_numeric
      (show 0 ≤ (0.503 : ℝ) * φ ^ 2 by positivity)
    linarith only [cos_lower, scaled, sq_nonneg φ]

private theorem shallowDevelopment_triangle_bound {φ : ℝ}
    (φ_nonneg : 0 ≤ φ) (φ_small : φ ≤ 0.1) :
    0 ≤ 2 * arcsin (tan (φ / 2) ^ 2) ∧
      2 * arcsin (tan (φ / 2) ^ 2) ≤ 0.502 * φ ^ 2 := by
  have half_nonneg : 0 ≤ φ / 2 := by positivity
  have half_small : φ / 2 ≤ 0.05 := by linarith only [φ_small]
  have cos_bound : 0.99875 ≤ cos (φ / 2) := by
    have sq := pow_le_pow_left₀ half_nonneg half_small 2
    linarith only [sq, one_sub_sq_div_two_le_cos (x := φ / 2)]
  have cos_pos : 0 < cos (φ / 2) := by linarith only [cos_bound]
  have tan_nonneg : 0 ≤ tan (φ / 2) := by
    rw [tan_eq_sin_div_cos]
    exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi half_nonneg (by
      linarith only [half_small, Real.pi_gt_three])) cos_pos.le
  have tan_bound : tan (φ / 2) ≤ 0.5007 * φ := by
    rw [tan_eq_sin_div_cos]
    apply (div_le_iff₀ cos_pos).2
    have sin_bound := Real.sin_le half_nonneg
    have prod := mul_le_mul_of_nonneg_left cos_bound (by positivity : 0 ≤ 0.5007 * φ)
    linarith only [prod, sin_bound, φ_nonneg]
  let a := (0.251 : ℝ) * φ ^ 2
  have a_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have a_small : a ≤ 0.00251 := by
    dsimp [a]
    linarith only [pow_le_pow_left₀ φ_nonneg φ_small 2]
  have a_sq : a ^ 2 ≤ (0.00251 : ℝ) ^ 2 := pow_le_pow_left₀ a_nonneg a_small 2
  have sin_lower : 0.999 * a ≤ sin a := by
    have prod := mul_le_mul_of_nonneg_left a_sq a_nonneg
    linarith only [sin_ge_sub_cube a_nonneg, prod, a_nonneg]
  have tan_sq_bound : tan (φ / 2) ^ 2 ≤ sin a := by
    have sq := pow_le_pow_left₀ tan_nonneg tan_bound 2
    dsimp [a] at sin_lower ⊢
    nlinarith only [sq, sin_lower, sq_nonneg φ]
  have arcsin_bound : arcsin (tan (φ / 2) ^ 2) ≤ a := by
    have interval : a ∈ Set.Icc (-(π / 2)) (π / 2) :=
      ⟨by linarith only [pi_pos, a_nonneg], by linarith only [a_small, pi_gt_three]⟩
    have input : tan (φ / 2) ^ 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith only [sq_nonneg (tan (φ / 2))], tan_sq_bound.trans (sin_le_one _)⟩
    exact (arcsin_le_iff_le_sin input interval).2 tan_sq_bound
  have arcsin_nonneg : 0 ≤ arcsin (tan (φ / 2) ^ 2) := by
    rw [← arcsin_zero]
    exact arcsin_le_arcsin (sq_nonneg _)
  constructor
  · positivity
  · dsimp [a] at arcsin_bound
    linarith only [arcsin_bound]

/-- The explicit square-root flatness hypothesis proves all three numerical
conditions for sharp development. -/
theorem sharp_development_threshold {γ φ C : ℝ}
    (γ_pos : 0 < γ) (γ_small : γ < 1) (φ_nonneg : 0 ≤ φ)
    (flat : φ ≤ √γ / 10) (C_nonneg : 0 ≤ C) (C_small : C ≤ 2) :
    let Ω := shallowDevelopmentCurvature φ
    let B := shallowDevelopmentHeading φ
    let E := radialBlockError (cos φ)⁻¹ B C (√(1 - γ ^ 2)) π
    let d := (γ - E) / (1 + E)
    let D := C * (cos φ)⁻¹ / (1 - E)
    E < γ ∧ 2 * Ω / π < (d - 3 * Ω * D) / (1 + 3 * Ω * D) ∧
      B + 3 * Ω < 2 * arcsin γ := by
  let Ω := shallowDevelopmentCurvature φ
  let B := shallowDevelopmentHeading φ
  let E := radialBlockError (cos φ)⁻¹ B C (√(1 - γ ^ 2)) π
  have square_upper : φ ^ 2 ≤ γ / 100 := by
    have sq := pow_le_pow_left₀ φ_nonneg flat 2
    rw [div_pow, Real.sq_sqrt γ_pos.le] at sq
    norm_num at sq
    exact sq
  have φ_small : φ ≤ 0.1 := (le_of_not_gt fun hb => by
    have sq := pow_lt_pow_left₀ hb (by norm_num : (0 : ℝ) ≤ 0.1) (by decide : (2 : ℕ) ≠ 0)
    linarith only [sq, square_upper, γ_small])
  obtain ⟨sec_ge, sec_le, sec_sub⟩ := shallowDevelopment_sec_bounds φ_nonneg φ_small
  obtain ⟨tri_nonneg, tri_le⟩ := shallowDevelopment_triangle_bound φ_nonneg φ_small
  have Ω_nonneg : 0 ≤ Ω := by
    dsimp [Ω, shallowDevelopmentCurvature]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one φ))
  have Ω_bound : Ω ≤ π * φ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (one_sub_sq_div_two_le_cos (x := φ))
      (by positivity : 0 ≤ 2 * π)
    dsimp [Ω, shallowDevelopmentCurvature]
    linarith only [h]
  have sin_nonneg := sin_nonneg_of_nonneg_of_le_pi φ_nonneg (by
    linarith only [φ_small, pi_gt_three])
  have sec_nonneg : 0 ≤ (cos φ)⁻¹ := zero_le_one.trans sec_ge
  have B_nonneg : 0 ≤ B := by
    dsimp [B, shallowDevelopmentHeading]
    have curv : 0 ≤ shallowDevelopmentCurvature φ := Ω_nonneg
    have diff := sub_nonneg.mpr sec_ge
    positivity
  have pi_bound : π ≤ 22 / 7 := by linarith only [pi_lt_d4]
  have B_bound : B ≤ 17 * φ ^ 2 := by
    have sec_cost := mul_le_mul_of_nonneg_left sec_sub (by positivity : 0 ≤ 2 * π)
    have sin_cost := mul_le_mul_of_nonneg_left (Real.sin_le φ_nonneg) (by positivity : 0 ≤ 6 * φ)
    have pi_cost := mul_le_mul_of_nonneg_right pi_bound (sq_nonneg φ)
    change 3 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * π * ((cos φ)⁻¹ - 1) +
      6 * φ * sin φ + 2 * Ω ≤ 17 * φ ^ 2
    linarith only [tri_le, sec_cost, sin_cost, Ω_bound, pi_cost, sq_nonneg φ]
  have E_nonneg : 0 ≤ E := radialBlockError_nonneg sec_ge B_nonneg C_nonneg (sqrt_nonneg _) pi_pos
  have E_bound : E ≤ ((1.006 + 34.204 * (1 + (100 / 157) * √(1 - γ ^ 2))) / 100) * γ := by
    let K := √(1 - γ ^ 2)
    have K_nonneg : 0 ≤ K := sqrt_nonneg _
    have inv_pi : 1 / π ≤ (50 / 157 : ℝ) := (div_le_iff₀ pi_pos).2 (by
      linarith only [pi_gt_d2])
    have head : C * K / π ≤ (100 / 157) * K := calc
      _ = C * K * (1 / π) := by ring
      _ ≤ 2 * K * (50 / 157) := by
        have one_pi_nonneg : 0 ≤ 1 / π := by positivity
        gcongr
      _ = _ := by ring
    have loss : E ≤ (1.006 + 34.204 * (1 + (100 / 157) * K)) * φ ^ 2 := by
      have speed_loss : C * ((cos φ)⁻¹ - 1) ≤ 1.006 * φ ^ 2 := calc
        _ ≤ 2 * (0.503 * φ ^ 2) := by gcongr
        _ = _ := by ring
      have turn_loss : (cos φ)⁻¹ * B * C * (1 + C * K / π) ≤
          34.204 * (1 + (100 / 157) * K) * φ ^ 2 := calc
        _ ≤ 1.006 * (17 * φ ^ 2) * 2 * (1 + (100 / 157) * K) := by gcongr
        _ = _ := by ring
      change C * ((cos φ)⁻¹ - 1) + (cos φ)⁻¹ * B * C * (1 + C * K / π) ≤ _
      linarith only [speed_loss, turn_loss]
    calc
      _ ≤ (1.006 + 34.204 * (1 + (100 / 157) * K)) * (γ / 100) :=
        loss.trans (mul_le_mul_of_nonneg_left square_upper (by positivity))
      _ = _ := by ring
  have Ω_small : Ω ≤ π * γ / 100 := Ω_bound.trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left square_upper pi_pos.le)
  have S_small : C * (cos φ)⁻¹ ≤ 2.012 := by
    calc
      _ ≤ (2 : ℝ) * 1.006 := mul_le_mul C_small sec_le sec_nonneg (by norm_num)
      _ = _ := by norm_num
  have radial := sharp_development_radial_margin γ_pos γ_small E_nonneg E_bound
    (mul_nonneg C_nonneg sec_nonneg) S_small Ω_nonneg Ω_small
  have γ_arcsin : γ ≤ arcsin γ :=
    (le_arcsin_iff_sin_le
      ⟨by linarith only [pi_pos, γ_pos], by linarith only [pi_gt_three, γ_small]⟩
      ⟨by linarith only [γ_pos], γ_small.le⟩).2 (Real.sin_le γ_pos.le)
  change E < γ ∧ _ ∧ B + 3 * Ω < 2 * arcsin γ
  refine ⟨radial.1, radial.2, ?_⟩
  have pi_cost := mul_le_mul_of_nonneg_right pi_bound (sq_nonneg φ)
  linarith only [B_bound, Ω_bound, pi_cost, square_upper, γ_pos, γ_arcsin]

/-- The uniform one-sided heading allowance for curves in an acute heading cone. -/
def acuteConeDevelopmentHeading (φ : ℝ) : ℝ :=
  3 * (2 * arcsin (tan (φ / 2) ^ 2)) + 4 * φ * sin φ + shallowDevelopmentCurvature φ

/-- Relative chord error from the uniform heading allowance and change of speed. -/
def acuteConeDevelopmentError (φ C : ℝ) : ℝ :=
  C * ((cos φ)⁻¹ - 1) + C * (cos φ)⁻¹ * acuteConeDevelopmentHeading φ

/-- The sharp acute-cone threshold at squared tilt `γ / 32`. The branch
budget still uses the full shallow-development allowance. -/
theorem sharp_acuteCone_development_threshold {γ φ C : ℝ}
    (γ_pos : 0 < γ) (γ_small : γ ≤ 1 / 5) (φ_nonneg : 0 ≤ φ)
    (flat : φ ^ 2 ≤ γ / 32) (C_nonneg : 0 ≤ C) (C_small : C ≤ √2) :
    let Ω := shallowDevelopmentCurvature φ
    let B := shallowDevelopmentHeading φ
    let E := acuteConeDevelopmentError φ C
    let d := (γ - E) / (1 + E)
    let D := C * (cos φ)⁻¹ / (1 - E)
    E < γ ∧ 2 * Ω / π < (d - 3 * Ω * D) / (1 + 3 * Ω * D) ∧
      B + 3 * Ω < 2 * arcsin γ := by
  let Ω := shallowDevelopmentCurvature φ
  let E := acuteConeDevelopmentError φ C
  let d := (γ - E) / (1 + E)
  let D := C * (cos φ)⁻¹ / (1 - E)
  have φ_small : φ ≤ 0.1 := le_of_not_gt fun above => by
    have sq := pow_lt_pow_left₀ above (by norm_num : (0 : ℝ) ≤ 0.1) (by decide : (2 : ℕ) ≠ 0)
    linarith only [sq, flat, γ_small]
  obtain ⟨sec_ge, sec_le, sec_sub⟩ := shallowDevelopment_sec_bounds φ_nonneg φ_small
  obtain ⟨tri_nonneg, tri_le⟩ := shallowDevelopment_triangle_bound φ_nonneg φ_small
  have sec_pos : 0 < (cos φ)⁻¹ := zero_lt_one.trans_le sec_ge
  have C_le : C ≤ 1.4143 := C_small.trans
    ((sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1.4143)).2 (by norm_num))
  have pi_bound : π ≤ 22 / 7 := by linarith only [pi_lt_d4]
  have pi_sq := mul_le_mul_of_nonneg_right pi_bound (sq_nonneg φ)
  have Ω_nonneg : 0 ≤ Ω :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one φ))
  have Ω_le : Ω ≤ π * φ ^ 2 := by
    have cosine := mul_le_mul_of_nonneg_left (one_sub_sq_div_two_le_cos (x := φ))
      (show 0 ≤ 2 * π by positivity)
    change 2 * π * (1 - cos φ) ≤ π * φ ^ 2
    linarith only [cosine]
  have sin_nonneg := sin_nonneg_of_nonneg_of_le_pi φ_nonneg (by
    linarith only [φ_small, pi_gt_three])
  have sin_le := mul_le_mul_of_nonneg_left (Real.sin_le φ_nonneg) φ_nonneg
  have cone_nonneg : 0 ≤ acuteConeDevelopmentHeading φ := by
    unfold acuteConeDevelopmentHeading
    have curvature : 0 ≤ shallowDevelopmentCurvature φ := Ω_nonneg
    positivity
  have cone_bound : acuteConeDevelopmentHeading φ ≤ (5.506 + 22 / 7) * φ ^ 2 := by
    unfold acuteConeDevelopmentHeading
    change 3 * (2 * arcsin (tan (φ / 2) ^ 2)) + 4 * φ * sin φ + Ω ≤ _
    linarith only [tri_le, sin_le, Ω_le, pi_sq]
  have speed_loss :
      C * ((cos φ)⁻¹ - 1) ≤ 1.4143 * (0.503 * φ ^ 2) := by gcongr
  have turn_loss :
      C * (cos φ)⁻¹ * acuteConeDevelopmentHeading φ ≤
        1.4143 * 1.006 * ((5.506 + 22 / 7) * φ ^ 2) := by gcongr
  have E_nonneg : 0 ≤ E := by
    unfold E acuteConeDevelopmentError
    exact add_nonneg (mul_nonneg C_nonneg (sub_nonneg.mpr sec_ge))
      (mul_nonneg (mul_nonneg C_nonneg sec_pos.le) cone_nonneg)
  have E_sq : E ≤ 13.1 * φ ^ 2 := by
    unfold E acuteConeDevelopmentError
    linarith only [speed_loss, turn_loss, sq_nonneg φ]
  have E_le : E ≤ 0.41 * γ := by linarith only [E_sq, flat, γ_pos]
  have E_lt : E < γ := by linarith only [E_le, γ_pos]
  have E_small : E ≤ 0.082 := by linarith only [E_le, γ_small]
  have d_lower : 0.545 * γ ≤ d := by
    apply (le_div_iff₀ (by linarith only [E_nonneg] : 0 < 1 + E)).mpr
    have numer := mul_le_mul_of_nonneg_left E_small (show 0 ≤ 0.545 * γ by positivity)
    linarith only [numer, E_le, γ_pos]
  have D_upper : D ≤ 1.55 := by
    apply (div_le_iff₀ (by linarith only [E_small] : 0 < 1 - E)).mpr
    have speed : C * (cos φ)⁻¹ ≤ (1.4143 : ℝ) * 1.006 :=
      mul_le_mul C_le sec_le sec_pos.le (by norm_num)
    linarith only [speed, E_small]
  have D_nonneg : 0 ≤ D :=
    div_nonneg (mul_nonneg C_nonneg sec_pos.le) (by linarith only [E_small])
  have curvature_bound : Ω ≤ π * γ / 32 := Ω_le.trans
    (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left flat pi_pos.le)
  have cost_bound : 3 * Ω * D ≤ 0.457 * γ := by
    have curvature : Ω ≤ (22 / 7) * γ / 32 := curvature_bound.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right pi_bound γ_pos.le) (by norm_num))
    calc
      _ ≤ (3 * ((22 / 7) * γ / 32)) * 1.55 := by gcongr
      _ ≤ _ := by linarith only [γ_pos]
  have cost_nonneg : 0 ≤ 3 * Ω * D := by positivity
  have cost_small : 3 * Ω * D ≤ 0.092 := by linarith only [cost_bound, γ_small]
  have bank_margin : γ / 16 < (d - 3 * Ω * D) / (1 + 3 * Ω * D) := by
    apply (lt_div_iff₀ (by linarith only [cost_nonneg] : 0 < 1 + 3 * Ω * D)).mpr
    have loss := mul_le_mul_of_nonneg_left cost_small (show 0 ≤ γ / 16 by positivity)
    linarith only [loss, d_lower, cost_bound, γ_pos]
  have curvature_small : 2 * Ω / π ≤ γ / 16 := by
    apply (div_le_iff₀ pi_pos).mpr
    linarith only [curvature_bound]
  refine ⟨E_lt, curvature_small.trans_lt bank_margin, ?_⟩
  have wide : shallowDevelopmentHeading φ ≤ 17 * φ ^ 2 := by
    have sec_cost := mul_le_mul_of_nonneg_left sec_sub (show 0 ≤ 2 * π by positivity)
    unfold shallowDevelopmentHeading
    change 3 * (2 * arcsin (tan (φ / 2) ^ 2)) + 2 * π * ((cos φ)⁻¹ - 1) +
      6 * φ * sin φ + 2 * Ω ≤ _
    linarith only [tri_le, sec_cost, sin_le, Ω_le, pi_sq, sq_nonneg φ]
  have γ_arcsin : γ ≤ arcsin γ :=
    (le_arcsin_iff_sin_le
      ⟨by linarith only [pi_pos, γ_pos], by linarith only [pi_gt_three, γ_small]⟩
      ⟨by linarith only [γ_pos], by linarith only [γ_small]⟩).2 (Real.sin_le γ_pos.le)
  change shallowDevelopmentHeading φ + 3 * Ω < 2 * arcsin γ
  linarith only [wide, Ω_le, pi_sq, flat, γ_pos, γ_arcsin]

end Unfoldings
