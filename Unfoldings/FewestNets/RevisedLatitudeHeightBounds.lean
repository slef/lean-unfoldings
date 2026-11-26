module

public import Unfoldings.FewestNets.RevisedLatitudeVertexBounds

/-! Absolute and relative height estimates of the annular triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- For corrections of a common sign, their difference is bounded by the
larger individual bound. -/
theorem abs_sub_le_of_same_sign {x y bound : ℝ} (x_bound : |x| ≤ bound)
    (y_bound : |y| ≤ bound) (sign : 0 ≤ x * y) :
    |x - y| ≤ bound := by
  rw [abs_le] at x_bound y_bound ⊢
  rcases mul_nonneg_iff.mp sign with ⟨one, two⟩ | ⟨one, two⟩ <;>
    constructor <;> linarith only [x_bound.1, x_bound.2, y_bound.1, y_bound.2, one, two]

/-- Opposite rows have opposite signed meridional heights. The common sign of
the two corrections keeps the error in their difference to one term. -/
theorem signed_height_bounds {d Z₀ Z₁ Y₀ Y₁ error : ℝ}
    (sine : 0 ≤ sin (d / 2))
    (z₀ : Z₀ ∈ Set.Icc (0.9612 : ℝ) 1) (z₁ : Z₁ ∈ Set.Icc (0.9612 : ℝ) 1)
    (near₀ : |Y₀ + sin (d / 2) / Z₀| ≤ error)
    (near₁ : |Y₁ - sin (d / 2) / Z₁| ≤ error)
    (sign : 0 ≤ (Y₀ + sin (d / 2) / Z₀) * (Y₁ - sin (d / 2) / Z₁)) :
    (2 * sin (d / 2) - error ≤ Y₁ - Y₀ ∧
      Y₁ - Y₀ ≤ 2 * sin (d / 2) / 0.9612 + error) ∧
    (sin (d / 2) - error ≤ -Y₀ ∧ -Y₀ ≤ sin (d / 2) / 0.9612 + error) ∧
    sin (d / 2) - error ≤ Y₁ ∧ Y₁ ≤ sin (d / 2) / 0.9612 + error := by
  have bounds {Z : ℝ} (hz : Z ∈ Set.Icc (0.9612 : ℝ) 1) :
      sin (d / 2) ≤ sin (d / 2) / Z ∧ sin (d / 2) / Z ≤ sin (d / 2) / 0.9612 :=
    ⟨by
      have p : 0 < Z := (by norm_num : (0 : ℝ) < 0.9612).trans_le hz.1
      exact (div_one (sin (d / 2))).symm.trans_le (div_le_div_of_nonneg_left sine p hz.2),
      div_le_div_of_nonneg_left sine (by norm_num) hz.1⟩
  have one := bounds z₀
  have two := bounds z₁
  have difference := abs_sub_le_of_same_sign near₁ near₀ (by nlinarith only [sign])
  rcases abs_le.mp difference with ⟨dl, du⟩
  rcases abs_le.mp near₀ with ⟨l₀, u₀⟩
  rcases abs_le.mp near₁ with ⟨l₁, u₁⟩
  have split : 2 * sin (d / 2) / 0.9612 =
      sin (d / 2) / 0.9612 + sin (d / 2) / 0.9612 := by ring
  rw [split]
  exact ⟨⟨by linarith only [dl, one.1, two.1],
      by linarith only [du, one.2, two.2]⟩,
    ⟨by linarith only [u₀, one.1], by linarith only [l₀, one.2]⟩,
    by linarith only [l₁, two.1], by linarith only [u₁, two.2]⟩

/-- The two bounds on the sine of half a band height. -/
theorem sine_half_step_bounds {r d : ℝ} (rp : 0 < r) (rs : r < 0.522)
    (lower : 0.852 * r ≤ d) (upper : d ≤ r) :
    (0.852 / 2) * (1 - (0.852 * 0.522 : ℝ) ^ 2 / 24) * r ≤ sin (d / 2) ∧
      sin (d / 2) ≤ d / 2 := by
  have zpos : 0 < 0.852 * r / 2 := by positivity
  have ypos : 0 ≤ d / 2 := le_of_lt (zpos.trans_le (by linarith only [lower]))
  refine ⟨?_, sin_le ypos⟩
  have sq := pow_le_pow_left₀ zpos.le
    (show 0.852 * r / 2 ≤ 0.852 * 0.522 / 2 by linarith only [rs]) 2
  have cube : (0.852 * r / 2) ^ 3 / 6 ≤ (0.852 * 0.522 : ℝ) ^ 2 / 24 * (0.852 * r / 2) := by
    rw [show (0.852 * r / 2) ^ 3 / 6 = ((0.852 * r / 2) ^ 2 / 6) * (0.852 * r / 2) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith only [sq]) zpos.le
  have linear : (0.852 / 2) * (1 - (0.852 * 0.522 : ℝ) ^ 2 / 24) * r ≤ sin (0.852 * r / 2) := by
    linarith only [sin_gt_sub_cube zpos, cube]
  apply linear.trans
  exact sin_le_sin_of_le_of_le_pi_div_two (by linarith only [zpos, pi_pos])
    (by linarith only [upper, rs, pi_gt_d2]) (by linarith only [lower])

/-- The revised signed heights give the chart shape in either type of strip. -/
theorem triangle_height_bounds {r b d Y₀ Y₁ : ℝ} (polar : Bool)
    (rp : 0 < r) (rs : r < 0.522) (bp : 0 < b) (bs : b < 0.268 * r)
    (dmin : 0.852 * r ≤ d) (dmax : d ≤ r)
    (height : (2 * sin (d / 2) - ordinateErrorFactor polar * b ^ 2 / r ≤ Y₁ - Y₀ ∧
      Y₁ - Y₀ ≤ 2 * sin (d / 2) / 0.9612 + ordinateErrorFactor polar * b ^ 2 / r) ∧
      (sin (d / 2) - ordinateErrorFactor polar * b ^ 2 / r ≤ -Y₀ ∧
        -Y₀ ≤ sin (d / 2) / 0.9612 + ordinateErrorFactor polar * b ^ 2 / r) ∧
      sin (d / 2) - ordinateErrorFactor polar * b ^ 2 / r ≤ Y₁ ∧
        Y₁ ≤ sin (d / 2) / 0.9612 + ordinateErrorFactor polar * b ^ 2 / r) :
    let hmin : ℝ := if polar then 0.815 else 0.834
    let hmax : ℝ := if polar then 1.070 else 1.051
    let ymin : ℝ := if polar then 0.393 else 0.412
    let ymax : ℝ := if polar then 0.550 else 0.531
    (hmin * r < Y₁ - Y₀ ∧ Y₁ - Y₀ < hmax * r) ∧
      (ymin * r < -Y₀ ∧ -Y₀ < ymax * r) ∧
      ymin * r < Y₁ ∧ Y₁ < ymax * r := by
  obtain ⟨sl, su⟩ := sine_half_step_bounds rp rs dmin dmax
  obtain ⟨⟨hl, hu⟩, ⟨ll, lu⟩, ul, uu⟩ := height
  have error : ordinateErrorFactor polar * b ^ 2 / r ≤ (ordinateErrorFactor polar * 0.268 ^ 2) * r := by
    apply (div_le_iff₀ rp).mpr
    have sq := pow_le_pow_left₀ bp.le bs.le 2
    have coef : 0 ≤ ordinateErrorFactor polar := by cases polar <;> norm_num [ordinateErrorFactor]
    have scaled := mul_le_mul_of_nonneg_left sq coef
    nlinarith only [scaled]
  have upper_sine : 2 * sin (d / 2) / 0.9612 ≤ 1.0404 * r := by
    apply (div_le_iff₀ (by norm_num)).mpr
    linarith only [su, dmax, rp]
  have upper_half : sin (d / 2) / 0.9612 ≤ 0.5202 * r := by
    apply (div_le_iff₀ (by norm_num)).mpr
    linarith only [su, dmax, rp]
  dsimp only
  cases polar <;> simp only [ordinateErrorFactor, Bool.false_eq_true, ite_false, ite_true] at hl hu ll lu ul uu error ⊢ <;>
    exact ⟨⟨by linarith only [hl, sl, error, rp], by linarith only [hu, upper_sine, error, rp]⟩,
      ⟨by linarith only [ll, sl, error, rp], by linarith only [lu, upper_half, error, rp]⟩,
      by linarith only [ul, sl, error, rp], by linarith only [uu, upper_half, error, rp]⟩

end Unfoldings.FewestNets.RevisedLatitudeGrid
