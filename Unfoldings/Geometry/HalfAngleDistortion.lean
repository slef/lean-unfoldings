module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Tactic

/-! Lower norm distortion for a linear map gives lower half-angle distortion. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry NormedSpace

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

private theorem norm_sub_eq_twice_sin_half_angle {u v : X} (unit_u : ‖u‖ = 1)
    (unit_v : ‖v‖ = 1) : ‖u - v‖ = 2 * sin (angle u v / 2) := by
  have θ := angle_nonneg u v
  have upper := angle_le_pi u v
  have nonnegative : 0 ≤ sin (angle u v / 2) := sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by linarith only [upper, pi_pos])
  have squared := norm_sub_pow_two_real u v
  rw [unit_u, unit_v, inner_eq_cos_angle_of_norm_eq_one unit_u unit_v,
    show angle u v = 2 * (angle u v / 2) by ring, cos_two_mul] at squared
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    (by nlinarith only [squared, sin_sq_add_cos_sq (angle u v / 2)])

private theorem norm_smul_sub_smul_ge_unit_chord {u v : X} (unit_u : ‖u‖ = 1)
    (unit_v : ‖v‖ = 1) {s t : ℝ} (s_one : 1 ≤ s) (t_one : 1 ≤ t) :
    ‖u - v‖ ≤ ‖s • u - t • v‖ := by
  have s_nonneg : 0 ≤ s := le_trans zero_le_one s_one
  have t_nonneg : 0 ≤ t := le_trans zero_le_one t_one
  have prod : 1 ≤ s * t := by nlinarith only [mul_nonneg (sub_nonneg.mpr s_one) t_nonneg, t_one]
  have longer := norm_sub_pow_two_real (s • u) (t • v)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg s_nonneg,
    abs_of_nonneg t_nonneg, unit_u, unit_v, mul_one, mul_one, real_inner_smul_left,
    real_inner_smul_right] at longer
  have chord := norm_sub_pow_two_real u v
  rw [unit_u, unit_v] at chord
  have exact_chord : ‖s • u - t • v‖ ^ 2 =
      (s - t) ^ 2 + (s * t) * ‖u - v‖ ^ 2 := by
    rw [longer, chord]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [exact_chord]
  have threshold := mul_le_mul_of_nonneg_right prod (sq_nonneg ‖u - v‖)
  nlinarith only [threshold, sq_nonneg (s - t)]

/-- A linear map with norm between `c` and one decreases the sine of half
the angle between two directions by at most the factor `c`. -/
theorem sin_half_angle_map_ge (T : X →ₗ[ℝ] Y) {c : ℝ} (c_pos : 0 < c)
    (lower : ∀ x, c * ‖x‖ ≤ ‖T x‖) (upper : ∀ x, ‖T x‖ ≤ ‖x‖)
    {u v : X} (u_ne : u ≠ 0) (v_ne : v ≠ 0) :
    c * sin (angle u v / 2) ≤ sin (angle (T u) (T v) / 2) := by
  let a := normalize u
  let b := normalize v
  have a_unit : ‖a‖ = 1 := norm_normalize u_ne
  have b_unit : ‖b‖ = 1 := norm_normalize v_ne
  have ta_pos : 0 < ‖T a‖ := by
    have qa := lower a
    rw [a_unit, mul_one] at qa
    exact c_pos.trans_le qa
  have tb_pos : 0 < ‖T b‖ := by
    have qb := lower b
    rw [b_unit, mul_one] at qb
    exact c_pos.trans_le qb
  have ta_unit : ‖normalize (T a)‖ = 1 := norm_normalize (norm_pos_iff.mp ta_pos)
  have tb_unit : ‖normalize (T b)‖ = 1 := norm_normalize (norm_pos_iff.mp tb_pos)
  have angle_a : angle a b = angle u v := by
    change angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) = _
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr u_ne)),
      angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr v_ne))]
  have angle_b : angle (normalize (T a)) (normalize (T b)) = angle (T u) (T v) := by
    change angle (‖T a‖⁻¹ • T (‖u‖⁻¹ • u)) (‖T b‖⁻¹ • T (‖v‖⁻¹ • v)) = _
    rw [map_smul, map_smul, smul_smul, smul_smul,
      angle_smul_left_of_pos _ _ (mul_pos (inv_pos.mpr ta_pos) (inv_pos.mpr (norm_pos_iff.mpr u_ne))),
      angle_smul_right_of_pos _ _ (mul_pos (inv_pos.mpr tb_pos) (inv_pos.mpr (norm_pos_iff.mpr v_ne)))]
  have s_one : 1 ≤ ‖T a‖⁻¹ := by
    have h := upper a
    rw [a_unit] at h
    exact (one_le_inv₀ ta_pos).mpr h
  have t_one : 1 ≤ ‖T b‖⁻¹ := by
    have h := upper b
    rw [b_unit] at h
    exact (one_le_inv₀ tb_pos).mpr h
  have source := mul_le_mul_of_nonneg_left
    (norm_smul_sub_smul_ge_unit_chord a_unit b_unit s_one t_one) c_pos.le
  have res := source.trans (lower (‖T a‖⁻¹ • a - ‖T b‖⁻¹ • b))
  rw [map_sub, map_smul, map_smul] at res
  change c * ‖a - b‖ ≤ ‖normalize (T a) - normalize (T b)‖ at res
  rw [norm_sub_eq_twice_sin_half_angle a_unit b_unit, norm_sub_eq_twice_sin_half_angle ta_unit tb_unit,
    angle_a, angle_b] at res
  linarith only [res]

end Unfoldings
