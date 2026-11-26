module

public import Unfoldings.FewestNets.RevisedLatitudeMetricRows
public import Unfoldings.FewestNets.LatitudeFrame

/-! Quantitative chart estimates for individual vertices of the revised latitude grid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The relative target interval for the row of the vertex. -/
def widthFactor (polar : Bool) : ℝ := if polar then 0.6 else 1

/-- The reciprocal circumference bound at the row of the vertex. -/
def inverseSineFactor (polar : Bool) : ℝ := if polar then 8.649 else 1.080

/-- Bounds on the ordinate correction. A strip touching a polar row uses the
larger value, also for its other row. -/
def ordinateErrorFactor (polar : Bool) : ℝ := if polar then 0.406 else 0.141

/-- The chart denominator and the east/south deviations, before assembling
opposite vertices into triangle heights. -/
theorem vertex_coordinates {r b ell row w : ℝ} (polar : Bool)
    (rp : 0 < r) (rs : r < 0.522)
    (bp : 0 < b) (bs : b < 0.268 * r)
    (within : |row - ell| ≤ r / 2)
    (mid_nonneg : 0 ≤ sin ell) (sine_pos : 0 < sin row)
    (radius_sine : r ≤ inverseSineFactor polar * sin row)
    (near : sin row * |w| ≤ widthFactor polar * b / 2) :
    let Z := latitudeDenominator ell row w
    let X := sin row * sin w / Z
    let Y := (sin (row - ell) - cos ell * sin row * (1 - cos w)) / Z
    0.9612 < Z ∧ Z ≤ cos (row - ell) ∧
      |X| < widthFactor polar * b / (2 * 0.9612) ∧
      |Y - sin (row - ell) / Z| ≤ ordinateErrorFactor polar * b ^ 2 / r := by
  let Z := latitudeDenominator ell row w
  let X := sin row * sin w / Z
  let Y := (sin (row - ell) - cos ell * sin row * (1 - cos w)) / Z
  let c := inverseSineFactor polar
  let f := widthFactor polar
  let E := ordinateErrorFactor polar
  have cp : 0 < c := by cases polar <;> norm_num [c, inverseSineFactor]
  have fp : 0 < f := by cases polar <;> norm_num [f, widthFactor]
  have ep : 0 < E := by cases polar <;> norm_num [E, ordinateErrorFactor]
  have cosine : 1 - cos w ≤ w ^ 2 / 2 := by linarith only [one_sub_sq_div_two_le_cos (x := w)]
  have cosine_nonneg : 0 ≤ 1 - cos w := sub_nonneg.mpr (cos_le_one _)
  have sine_diff := abs_sin_sub_sin_le ell row
  rw [abs_sub_comm ell row] at sine_diff
  have sine_scale : sin ell ≤ (1 + c / 2) * sin row := by
    linarith only [(le_abs_self (sin ell - sin row)).trans (sine_diff.trans within), radius_sine]
  have near' : sin ell * |w| ≤ (1 + c / 2) * (f * b / 2) := by
    calc
      _ ≤ ((1 + c / 2) * sin row) * |w| :=
        mul_le_mul_of_nonneg_right sine_scale (abs_nonneg _)
      _ = (1 + c / 2) * (sin row * |w|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left near (by positivity)
  have loss : sin row * sin ell * (1 - cos w) ≤ (1 + c / 2) * (f ^ 2 * b ^ 2) / 8 := by
    have factor := mul_le_mul_of_nonneg_left cosine (mul_nonneg sine_pos.le mid_nonneg)
    have prod := mul_le_mul near near' (mul_nonneg mid_nonneg (abs_nonneg _))
      (by positivity : 0 ≤ f * b / 2)
    rw [← sq_abs w] at factor
    nlinarith only [factor, prod]
  have near_sq := pow_le_pow_left₀ (abs_nonneg (row - ell)) within 2
  rw [sq_abs] at near_sq
  have z_lower : 0.9612 < Z := by
    have radius_sq := pow_le_pow_left₀ rp.le rs.le 2
    have bmax : b < 0.268 * 0.522 := bs.trans
      (mul_lt_mul_of_pos_left rs (by norm_num))
    have b_sq := pow_le_pow_left₀ bp.le bmax.le 2
    have cosine := one_sub_sq_div_two_le_cos (x := row - ell)
    change 0.9612 < cos (row - ell) - sin row * sin ell * (1 - cos w)
    cases polar <;> simp only [c, f, inverseSineFactor, widthFactor, Bool.false_eq_true,
      ite_false, ite_true] at loss <;>
      nlinarith only [loss, near_sq, radius_sq, b_sq, cosine]
  have zp : 0 < Z := (by norm_num : (0 : ℝ) < 0.9612).trans z_lower
  have upper : Z ≤ cos (row - ell) :=
    sub_le_self _ (mul_nonneg (mul_nonneg sine_pos.le mid_nonneg) cosine_nonneg)
  have horizontal : |X| < f * b / (2 * 0.9612) := by
    change |sin row * sin w / Z| < _
    rw [abs_div, abs_mul, abs_of_pos zp, abs_of_pos sine_pos]
    apply (div_lt_iff₀ zp).mpr
    have h := (mul_le_mul_of_nonneg_left (abs_sin_le_abs (x := w)) sine_pos.le).trans near
    have bound := mul_lt_mul_of_pos_left z_lower (show 0 < f * b / (2 * 0.9612) by positivity)
    have id : f * b / (2 * 0.9612) * 0.9612 = f * b / 2 := by ring
    rw [id] at bound
    exact h.trans_lt bound
  have vertical : |Y - sin (row - ell) / Z| ≤ E * b ^ 2 / r := by
    have equal : Y - sin (row - ell) / Z = -(cos ell * sin row * (1 - cos w)) / Z := by
      dsimp only [Y]
      rw [← sub_div, sub_sub_cancel_left]
    rw [equal, abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos zp, abs_of_pos sine_pos,
      abs_of_nonneg cosine_nonneg]
    have numerator : sin row * (1 - cos w) ≤ (f * b) ^ 2 / (8 * sin row) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have square := pow_le_pow_left₀ (mul_nonneg sine_pos.le (abs_nonneg w)) near 2
      have scaled := mul_le_mul_of_nonneg_left cosine (show 0 ≤ 8 * sin row ^ 2 by positivity)
      rw [← sq_abs w] at scaled
      nlinarith only [square, scaled]
    have inverse : f ^ 2 * r ≤ E * (8 * sin row * Z) := by
      have lower := mul_le_mul_of_nonneg_left z_lower.le (show 0 ≤ 8 * sin row by positivity)
      have scale := mul_le_mul_of_nonneg_left radius_sine (sq_nonneg f)
      have err := mul_le_mul_of_nonneg_left lower ep.le
      cases polar <;> simp only [f, E, widthFactor, inverseSineFactor, ordinateErrorFactor,
        Bool.false_eq_true, ite_false, ite_true] at scale err ⊢ <;>
        nlinarith only [scale, err, sine_pos]
    calc
      _ ≤ (sin row * (1 - cos w)) / Z := by
        apply div_le_div_of_nonneg_right _ zp.le
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (abs_cos_le_one ell) sine_pos.le) cosine_nonneg
        simpa only [one_mul] using h
      _ ≤ ((f * b) ^ 2 / (8 * sin row)) / Z :=
        div_le_div_of_nonneg_right numerator zp.le
      _ ≤ _ := by
        rw [div_div]
        apply (div_le_div_iff₀ (by positivity) rp).mpr
        have h := mul_le_mul_of_nonneg_right inverse (sq_nonneg b)
        nlinarith only [h]
  exact ⟨z_lower, upper, horizontal, vertical⟩

end Unfoldings.FewestNets.RevisedLatitudeGrid
