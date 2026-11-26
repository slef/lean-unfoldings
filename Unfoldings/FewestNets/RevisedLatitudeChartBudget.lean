module

public import Unfoldings.FewestNets.RevisedLatitudePairShape
public import Unfoldings.FewestNets.RevisedLatitudeRoutingScalars

/-! Normalize the chart dimensions once for the routing and counting proofs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The actual normalized height of a band. -/
def relativeStep (a : ℝ) : ℝ := rowStep a / radius a

/-- A common bound for the magnitude of both ordinates. -/
def ordinateBound (a : ℝ) (polar : Bool) : ℝ :=
  radius a * (relativeStep a / (2 * 0.9612) + ordinateErrorFactor polar * 0.268 ^ 2)

theorem relativeStep_bounds {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0.852 ≤ relativeStep a ∧ relativeStep a ≤ 1 := by
  have h := rowStep_bounds positive small
  have rp := radius_pos positive
  exact ⟨(le_div_iff₀ rp).mpr h.1.le, (div_le_one rp).mpr h.2⟩

theorem rowStep_eq_relativeStep_mul_radius {a : ℝ} (positive : 0 < a) :
    relativeStep a * radius a = rowStep a :=
  div_mul_cancel₀ _ (radius_pos positive).ne'

theorem ordinateErrorFactor_nonneg (polar : Bool) : 0 ≤ ordinateErrorFactor polar := by
  cases polar <;> norm_num [ordinateErrorFactor]

private theorem normalized_error_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (polar : Bool) :
    ordinateErrorFactor polar * spacing a ^ 2 / radius a ≤
      (ordinateErrorFactor polar * 0.268 ^ 2) * radius a := by
  have sq := pow_le_pow_left₀ (spacing_pos positive).le (spacing_lt positive small).le 2
  apply (div_le_iff₀ (radius_pos positive)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left sq (ordinateErrorFactor_nonneg polar)]

/-- The exact sine bounds imply the affine height and ordinate budgets. -/
theorem affine_height_bounds {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (polar : Bool) {H Y₀ Y₁ : ℝ}
    (low : 2 * sin (rowStep a / 2) - ordinateErrorFactor polar * spacing a ^ 2 / radius a ≤ H)
    (high : H ≤ 2 * sin (rowStep a / 2) / 0.9612 +
      ordinateErrorFactor polar * spacing a ^ 2 / radius a)
    (bottom : -Y₀ ≤ sin (rowStep a / 2) / 0.9612 +
      ordinateErrorFactor polar * spacing a ^ 2 / radius a)
    (top : Y₁ ≤ sin (rowStep a / 2) / 0.9612 +
      ordinateErrorFactor polar * spacing a ^ 2 / radius a) :
    heightDenominator polar (relativeStep a) * radius a ≤ 0.9612 * H ∧
      H ≤ radius a * (relativeStep a / 0.9612 + ordinateErrorFactor polar * 0.268 ^ 2) ∧
      -Y₀ ≤ ordinateBound a polar ∧ Y₁ ≤ ordinateBound a polar := by
  have dp := rowStep_pos positive small
  have du := (rowStep_bounds positive small).2
  have square := pow_le_pow_left₀ (half_pos dp).le
    (show rowStep a / 2 ≤ 0.522 / 2 by linarith only [du, radius_lt small]) 2
  have cube : (rowStep a / 2) ^ 3 / 6 ≤ (0.522 : ℝ) ^ 2 / 24 * (rowStep a / 2) := by
    nlinarith only [mul_le_mul_of_nonneg_right square (half_pos dp).le]
  have lo := sin_gt_sub_cube (half_pos dp)
  have hi := sin_le (half_pos dp).le
  have err := normalized_error_le positive small polar
  have eq := rowStep_eq_relativeStep_mul_radius positive
  unfold heightDenominator ordinateBound
  constructor
  · nlinarith only [low, lo, cube, err, eq]
  have normalize (z : ℝ) :
      radius a * (relativeStep a / z + ordinateErrorFactor polar * 0.268 ^ 2) =
        rowStep a / z + (ordinateErrorFactor polar * 0.268 ^ 2) * radius a := by
    rw [← eq]
    ring
  rw [normalize, normalize]
  have scaled := div_le_div_of_nonneg_right hi (by norm_num : (0 : ℝ) ≤ 0.9612)
  rw [div_div] at scaled
  ring_nf at scaled high bottom top err ⊢
  exact ⟨by linarith only [high, scaled, err], by linarith only [bottom, scaled, err],
    by linarith only [top, scaled, err]⟩

/-- The positive denominator in the normalized apex and side bounds. -/
theorem heightDenominator_relativeStep_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (polar : Bool) : 0 < heightDenominator polar (relativeStep a) := by
  have low := (relativeStep_bounds positive small).1
  cases polar <;> norm_num [heightDenominator, ordinateErrorFactor] <;> linarith only [low]

/-- The enclosing rectangle gives the common tilt and projection budget. -/
theorem rectangle_tilt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) (polar : Bool) :
    let X := spacing a / (2 * 0.9612)
    let Y := ordinateBound a polar
    ∃ φ : ℝ, 0 < φ ∧ φ ≤ 0.297 ∧
      0.512 * φ ^ 2 ≤ a * distortionFactor polar (relativeStep a) ∧
      X ^ 2 + Y ^ 2 = (tan φ) ^ 2 := by
  let X := spacing a / (2 * 0.9612)
  let Y := ordinateBound a polar
  let L := √(X ^ 2 + Y ^ 2)
  let φ := arctan L
  have Xp : 0 < X := div_pos (spacing_pos positive) (by norm_num)
  have Yp : 0 < Y := by
    have xp := (relativeStep_bounds positive small).1
    have ep := mul_nonneg (ordinateErrorFactor_nonneg polar) (sq_nonneg (0.268 : ℝ))
    exact mul_pos (radius_pos positive)
      (add_pos_of_pos_of_nonneg (div_pos (by linarith only [xp]) (by norm_num)) ep)
  have point : 0 < X ^ 2 + Y ^ 2 := by positivity
  have Lp : 0 < L := sqrt_pos.mpr point
  have Lsq : L ^ 2 = X ^ 2 + Y ^ 2 := sq_sqrt point.le
  have φp : 0 < φ := arctan_pos.mpr Lp
  have φle : φ ≤ L := arctan_le_self Lp.le
  have xp : X ≤ (0.268 / (2 * 0.9612)) * radius a := by
    dsimp only [X]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (spacing_lt positive small).le (by norm_num)
  have rsq : radius a ^ 2 = 0.72 ^ 2 * a := by
    rw [radius, mul_pow, sq_sqrt positive.le]
  have Xsq := pow_le_pow_left₀ Xp.le xp 2
  have bound : 0.512 * φ ^ 2 ≤ a * distortionFactor polar (relativeStep a) := by
    have sq := pow_le_pow_left₀ φp.le φle 2
    have algebra : a * distortionFactor polar (relativeStep a) =
        0.512 * (((0.268 / (2 * 0.9612)) * radius a) ^ 2 + Y ^ 2) := by
      unfold distortionFactor Y ordinateBound
      simp only [mul_pow, rsq]
      ring
    rw [algebra]
    linarith only [sq, Lsq, Xsq]
  have ym : Y ≤ (0.550 : ℝ) * radius a := by
    unfold Y ordinateBound
    rw [mul_comm (0.550 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (radius_pos positive).le
    have xu := div_le_div_of_nonneg_right (relativeStep_bounds positive small).2
      (show (0 : ℝ) ≤ 2 * 0.9612 by norm_num)
    cases polar <;> norm_num [ordinateErrorFactor] at xu ⊢ <;> linarith only [xu]
  have xb : X ≤ 0.140 * radius a := by
    linarith only [xp, radius_pos positive]
  have xq := pow_le_pow_left₀ Xp.le xb 2
  have yq := pow_le_pow_left₀ Yp.le ym 2
  have rq := pow_le_pow_left₀ (radius_pos positive).le (radius_lt small).le 2
  have Lcap : L ≤ 0.297 := by
    apply (sq_le_sq₀ Lp.le (by norm_num)).mp
    rw [Lsq]
    nlinarith only [xq, yq, rq]
  refine ⟨φ, φp, φle.trans Lcap, bound, ?_⟩
  rw [show φ = arctan L from rfl, tan_arctan, Lsq]

end Unfoldings.FewestNets.RevisedLatitudeGrid
