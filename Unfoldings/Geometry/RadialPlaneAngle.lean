module

public import Unfoldings.Geometry.RadialChordBounds
public import Unfoldings.Geometry.SphericalPathAngle

/-! Angular distance in a radial image is at most planar distance divided by plane height. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open NormedSpace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The entire straight line lies in the supporting plane, so the normalized
curve has chord speed at most the original speed divided by the height. -/
theorem angle_normalize_le_div_planeHeight {n a b : E} {h : ℝ}
    (unit : ‖n‖ = 1) (hpos : 0 < h) (ha : inner ℝ n a = h) (hb : inner ℝ n b = h) :
    angle (NormedSpace.normalize a) (NormedSpace.normalize b) ≤ ‖b - a‖ / h := by
  let p (t : ℝ) := a + t • (b - a)
  let f (t : ℝ) := NormedSpace.normalize (p t)
  have height (t : ℝ) : inner ℝ n (p t) = h := by
    dsimp only [p]
    rw [inner_add_right, real_inner_smul_right, inner_sub_right, ha, hb, sub_self,
      mul_zero, add_zero]
  have low (t : ℝ) : h ≤ ‖p t‖ := by
    have bound := abs_real_inner_le_norm n (p t)
    rw [height, abs_of_pos hpos, unit, one_mul] at bound
    exact bound
  have nz (t : ℝ) : p t ≠ 0 := norm_pos_iff.mp (hpos.trans_le (low t))
  have chord (u v : ℝ) : ‖f v - f u‖ ≤ (‖b - a‖ / h) * |v - u| := by
    have product : h ^ 2 ≤ ‖p v‖ * ‖p u‖ := by
      rw [pow_two]
      exact mul_le_mul (low v) (low u) hpos.le (norm_nonneg _)
    have d : h ^ 2 * ‖f v - f u‖ ^ 2 ≤ ‖p v - p u‖ ^ 2 := by
      have bound := mul_le_mul_of_nonneg_right product (sq_nonneg ‖f v - f u‖)
      change h ^ 2 * ‖f v - f u‖ ^ 2 ≤
        ‖p v‖ * ‖p u‖ * ‖NormedSpace.normalize (p v) - NormedSpace.normalize (p u)‖ ^ 2 at bound
      rw [norm_mul_norm_mul_normalize_sub_sq (nz v) (nz u)] at bound
      exact bound.trans (sub_le_self _ (sq_nonneg _))
    have small : ‖f v - f u‖ ≤ ‖p v - p u‖ / h := by
      apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hpos.le)).mp
      rw [div_pow, le_div_iff₀ (pow_pos hpos _), mul_comm]
      exact d
    have displacement : p v - p u = (v - u) • (b - a) := by
      dsimp only [p]
      module
    rw [displacement, norm_smul, Real.norm_eq_abs] at small
    exact small.trans_eq (by ring)
  have result := angle_le_chord_speed f (fun t => norm_normalize (nz t))
    (div_nonneg (norm_nonneg _) hpos.le) chord 0 1
  simpa only [f, p, zero_smul, add_zero, one_smul, show a + (b - a) = b by abel, sub_zero,
    abs_one, mul_one] using result

end Unfoldings
