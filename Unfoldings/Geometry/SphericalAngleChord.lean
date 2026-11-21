module

public import Unfoldings.Geometry.SphericalEndpointLocality
public import Mathlib.Tactic

/-! Spherical angles are estimated arbitrarily closely by small chords. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

/-- The chord expression is twice the tangent of half the side angle. -/
theorem angle_le_chord_arcUpper_of_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (unit_x : ‖x‖ = 1) (unit_y : ‖y‖ = 1)
    (small : angle x y < π) :
    angle x y ≤ ‖y - x‖ / sqrt (1 - ‖y - x‖ ^ 2 / 4) := by
  let t := angle x y / 2
  have nonnegative : 0 ≤ t := div_nonneg (angle_nonneg _ _) (by norm_num)
  have half_lt : t < π / 2 := by dsimp [t]; linarith
  have sin_pos : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos])
  have cos_pos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], half_lt⟩
  have angle_eq : angle x y = 2 * t := by dsimp [t]; ring
  have chord := norm_sub_pow_two_real y x
  rw [unit_x, unit_y, inner_eq_cos_angle_of_norm_eq_one unit_y unit_x, angle_comm y x,
    angle_eq, cos_two_mul] at chord
  have root : sqrt (1 - ‖y - x‖ ^ 2 / 4) = cos t := by
    rw [show 1 - ‖y - x‖ ^ 2 / 4 = cos t ^ 2 by linarith only [chord],
      sqrt_sq cos_pos.le]
  have length : ‖y - x‖ = 2 * sin t :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (by
      nlinarith only [chord, sin_sq_add_cos_sq t])
  rw [root, length, mul_div_assoc, ← tan_eq_sin_div_cos]
  have tan := le_tan nonnegative half_lt
  dsimp [t] at tan
  linarith only [tan]

/-- Tiny chords of a unit sphere bound angles up to an arbitrarily small factor. -/
theorem exists_angle_le_one_add_mul_chord {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ε : ℝ} (pos : 0 < ε) :
    ∃ δ > 0, ∀ {x y : E}, ‖x‖ = 1 → ‖y‖ = 1 → ‖y - x‖ ≤ δ →
      angle x y ≤ (1 + ε) * ‖y - x‖ := by
  let d := (1 + ε)⁻¹
  have d_pos : 0 < d := by dsimp [d]; positivity
  have d_small : d < 1 := by
    dsimp [d]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have deltapos : 0 < 1 - d ^ 2 := by nlinarith [sq_lt_sq₀ d_pos.le zero_le_one |>.mpr d_small]
  refine ⟨sqrt (1 - d ^ 2), sqrt_pos.mpr deltapos, fun {x y} hx hy hc => ?_⟩
  have delta_le : sqrt (1 - d ^ 2) ≤ 1 := by
    apply (sqrt_le_left zero_le_one).mpr
    nlinarith
  have small : angle x y < π := by
    apply lt_of_le_of_ne (angle_le_pi _ _)
    intro eq
    have chord := norm_sub_eq_add_norm_of_angle_eq_pi (x := x) (y := y) eq
    rw [hx, hy, norm_sub_rev] at chord
    linarith [hc.trans delta_le]
  have square := (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mpr hc
  rw [sq_sqrt deltapos.le] at square
  have root : d ≤ sqrt (1 - ‖y - x‖ ^ 2 / 4) := by
    apply le_sqrt_of_sq_le
    linarith only [square, sq_nonneg ‖y - x‖]
  have cone := mul_le_mul_of_nonneg_right root
    (show 0 ≤ (1 + ε) * ‖y - x‖ by positivity)
  have cancel : d * ((1 + ε) * ‖y - x‖) = ‖y - x‖ := by
    dsimp [d]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (1 + ε : ℝ) ≠ 0), one_mul]
  rw [cancel, mul_comm] at cone
  exact (angle_le_chord_arcUpper_of_unit hx hy small).trans
    ((div_le_iff₀ (d_pos.trans_le root)).mpr cone)

end Unfoldings
