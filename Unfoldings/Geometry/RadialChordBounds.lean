module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

/-! Bounds for the chord lengths of radial projections of a planar mesh. -/

@[expose] public section

namespace Unfoldings

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_in_tangent_plane {n x : E} {h : ℝ}
    (unit : ‖n‖ = 1) (height : inner ℝ n x = h) (length : ‖x‖ ≤ 1) (hle : h ≤ 1)
    (hpos : 0 ≤ h) :
    ‖x - h • n‖ ≤ Real.sqrt (1 - h ^ 2) * ‖x‖ := by
  have hsq : 0 ≤ 1 - h ^ 2 := by nlinarith only [hpos, hle, mul_nonneg hpos (sub_nonneg.mpr hle)]
  have sq : ‖x - h • n‖ ^ 2 = ‖x‖ ^ 2 - h ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm n x, height, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hpos, unit]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sq, mul_pow, Real.sq_sqrt hsq]
  have lenSq : ‖x‖ ^ 2 ≤ 1 := by
    nlinarith only [length, norm_nonneg x, mul_nonneg (norm_nonneg x) (sub_nonneg.mpr length)]
  nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr lenSq)]

/-- Points in one plane inside the unit ball have a smaller radial distance
difference than their chord length, with a factor controlled by the plane height. -/
theorem abs_norm_sub_norm_le_of_plane {n x y : E} {h : ℝ}
    (unit : ‖n‖ = 1) (heightX : inner ℝ n x = h) (heightY : inner ℝ n y = h)
    (radiusX : ‖x‖ ≤ 1) (radiusY : ‖y‖ ≤ 1) (hpos : 0 < h) (hle : h ≤ 1) :
    |‖x‖ - ‖y‖| ≤ Real.sqrt (1 - h ^ 2) * ‖x - y‖ := by
  have nonzero : x ≠ 0 := by
    intro eq
    rw [eq, inner_zero_right] at heightX
    exact hpos.ne' heightX.symm
  have norm_pos : 0 < ‖x‖ + ‖y‖ :=
    add_pos_of_pos_of_nonneg (norm_pos_iff.mpr nonzero) (norm_nonneg y)
  apply (mul_le_mul_iff_of_pos_right norm_pos).mp
  let X := x - h • n
  let Y := y - h • n
  have diff : inner ℝ (X + Y) (x - y) = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by
    dsimp only [X, Y]
    rw [inner_sub_right]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, heightX, heightY]
    rw [real_inner_comm x y]
    ring
  have lengthX := norm_in_tangent_plane unit heightX radiusX hle hpos.le
  have lengthY := norm_in_tangent_plane unit heightY radiusY hle hpos.le
  calc
    |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) = |inner ℝ (X + Y) (x - y)| := by
      rw [diff, abs_mul, abs_of_pos norm_pos]
    _ ≤ ‖X + Y‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖X‖ + ‖Y‖) * ‖x - y‖ := mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ ≤ (Real.sqrt (1 - h ^ 2) * ‖x‖ + Real.sqrt (1 - h ^ 2) * ‖y‖) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (add_le_add lengthX lengthY) (norm_nonneg _)
    _ = (Real.sqrt (1 - h ^ 2) * ‖x - y‖) * (‖x‖ + ‖y‖) := by ring

theorem norm_mul_norm_mul_normalize_sub_sq {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖y‖ * ‖normalize x - normalize y‖ ^ 2 =
      ‖x - y‖ ^ 2 - (‖x‖ - ‖y‖) ^ 2 := by
  rw [norm_sub_sq_real, norm_normalize hx, norm_normalize hy, norm_sub_sq_real,
    NormedSpace.normalize, NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr hx, norm_ne_zero_iff.mpr hy]
  ring

/-- On a plane at positive height, the normalized chord length satisfies
both a sharp lower comparison and the unnormalized-chord upper comparison. -/
theorem normalized_chord_sq_bounds {n x y : E} {h : ℝ}
    (unit : ‖n‖ = 1) (heightX : inner ℝ n x = h) (heightY : inner ℝ n y = h)
    (radiusX : ‖x‖ ≤ 1) (radiusY : ‖y‖ ≤ 1) (hpos : 0 < h) (hle : h ≤ 1) :
    h ^ 2 * ‖x - y‖ ^ 2 ≤ ‖x‖ * ‖y‖ * ‖normalize x - normalize y‖ ^ 2 ∧
      ‖x‖ * ‖y‖ * ‖normalize x - normalize y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have ne {p : E} (hp : inner ℝ n p = h) : p ≠ 0 := by
    rintro rfl
    rw [inner_zero_right] at hp
    exact hpos.ne' hp.symm
  rw [norm_mul_norm_mul_normalize_sub_sq (ne heightX) (ne heightY)]
  have bound := abs_norm_sub_norm_le_of_plane unit heightX heightY radiusX radiusY hpos hle
  have squared := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr bound
  have hsq : 0 ≤ 1 - h ^ 2 := by nlinarith only [hpos, hle, mul_nonneg hpos.le (sub_nonneg.mpr hle)]
  rw [sq_abs, mul_pow, Real.sq_sqrt hsq] at squared
  exact ⟨by nlinarith only [squared], sub_le_self _ (sq_nonneg _)⟩

end Unfoldings
