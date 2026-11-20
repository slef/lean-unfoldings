module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Tactic.Linarith

/-! Fixed-radius angular speed of a rotating suffix at one of its contacts. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

/-- A fixed-circle velocity separates into the hinge rotation velocity and a
slide along the suffix tangent. Eliminating the slide gives the angular speed
as the ratio of the two radial scalar products. -/
theorem hingeCircle_angularSpeed_eq {p h v w : E} {slide : ℝ}
    (transverse : 0 < inner ℝ p v)
    (velocity : w = o.rightAngleRotation (p - h) + slide • v)
    (tangent : inner ℝ p w = 0) :
    o.areaForm p w / ‖p‖ ^ 2 = inner ℝ v (p - h) / inner ℝ p v := by
  have p_ne : p ≠ 0 := by
    intro zero
    simp [zero] at transverse
  have contact := o.inner_mul_areaForm_sub p v w
  rw [tangent, mul_zero, sub_zero] at contact
  have rotation : o.areaForm v w = inner ℝ v (p - h) := by
    rw [velocity, map_add, map_smul, o.areaForm_apply_self, smul_zero, add_zero,
      o.areaForm_rightAngleRotation_right]
  rw [rotation] at contact
  apply (div_eq_div_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr p_ne)) transverse.ne').mpr
  linarith only [contact]

/-- If the radial margin is at least `m` and the hinge is inside the contact
circle, the angular speed is at most `2 / m`. The same formula proves positive
motion when the tangent points strictly away from the hinge. -/
theorem hingeCircle_angularSpeed_le {p h v w : E} {slide m : ℝ}
    (m_pos : 0 < m) (p_ne : p ≠ 0) (v_ne : v ≠ 0)
    (margin : m * (‖p‖ * ‖v‖) ≤ inner ℝ p v) (hinge : ‖h‖ ≤ ‖p‖)
    (velocity : w = o.rightAngleRotation (p - h) + slide • v)
    (tangent : inner ℝ p w = 0) :
    o.areaForm p w / ‖p‖ ^ 2 ≤ 2 / m := by
  have transverse : 0 < inner ℝ p v :=
    (mul_pos m_pos (mul_pos (norm_pos_iff.mpr p_ne) (norm_pos_iff.mpr v_ne))).trans_le margin
  rw [hingeCircle_angularSpeed_eq o transverse velocity tangent]
  have norm : ‖p - h‖ ≤ 2 * ‖p‖ := (norm_sub_le _ _).trans (by linarith)
  have upper := (real_inner_le_norm v (p - h)).trans
    (mul_le_mul_of_nonneg_left norm (norm_nonneg v))
  apply (div_le_div_iff₀ transverse m_pos).mpr
  have control := mul_le_mul_of_nonneg_right upper m_pos.le
  linarith only [control, margin]

theorem hingeCircle_angularSpeed_pos {p h v w : E} {slide : ℝ}
    (transverse : 0 < inner ℝ p v) (away : 0 < inner ℝ v (p - h))
    (velocity : w = o.rightAngleRotation (p - h) + slide • v)
    (tangent : inner ℝ p w = 0) :
    0 < o.areaForm p w / ‖p‖ ^ 2 := by
  rw [hingeCircle_angularSpeed_eq o transverse velocity tangent]
  exact div_pos away transverse

end Unfoldings
