module

public import Unfoldings.Geometry.RadialRightCorner

/-! Original bank arclength parameters in their actual oriented corner frames. -/

@[expose] public section

namespace Unfoldings

/-- Forward original bank arclength is the positive real axis in the occupied left frame. -/
theorem radialLeftCornerFrame_real_length (radial direction : ℂ)
    (radial_ne : radial ≠ 0) (direction_ne : direction ≠ 0) (t : ℝ) :
    radialLeftCornerFrame radial direction ((t * ‖direction‖ : ℝ) : ℂ) = t • direction := by
  change polarRay (radial.arg + (direction / radial).arg) *
    ((t * ‖direction‖ : ℝ) : ℂ) = t • direction
  rw [polarRay_arg_add_arg_div radial direction radial_ne direction_ne,
    Complex.ofReal_mul, Complex.real_smul]
  have nonzero : (‖direction‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr direction_ne)
  field_simp

/-- Forward arclength is reversed in the occupied right frame, preserving its actual side. -/
theorem radialRightCornerFrame_real_length (radial direction : ℂ)
    (radial_ne : radial ≠ 0) (direction_ne : direction ≠ 0) (t : ℝ) :
    radialRightCornerFrame radial direction ((t * ‖direction‖ : ℝ) : ℂ) =
      t • (-direction) := by
  simpa only [radialRightCornerFrame, norm_neg] using
    radialLeftCornerFrame_real_length (-radial) (-direction) (neg_ne_zero.mpr radial_ne)
      (neg_ne_zero.mpr direction_ne) t

/-- The left frame's terminal ray follows the original incoming edge in reverse,
at exactly its original arclength. -/
theorem radialLeftCornerFrame_terminal_length (radial incoming outgoing : ℂ)
    (radial_ne : radial ≠ 0) (incoming_ne : incoming ≠ 0) (t : ℝ) :
    radialLeftCornerFrame radial outgoing
      ((t * ‖incoming‖) • polarRay (radialLeftCornerWidth radial incoming outgoing)) =
        t • (-incoming) := by
  let F := radialLeftCornerFrame radial outgoing
  let width := radialLeftCornerWidth radial incoming outgoing
  have terminal : F (polarRay width) = -incoming / (‖incoming‖ : ℂ) := by
    change polarRay (radial.arg + (outgoing / radial).arg) * polarRay width = _
    rw [← polarRay_add]
    have angle : radial.arg + (outgoing / radial).arg + width =
        radial.arg + (incoming / radial).arg + Real.pi := by
      dsimp [width, radialLeftCornerWidth]
      ring
    have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
    rw [angle, polarRay_add,
      polarRay_arg_add_arg_div radial incoming radial_ne incoming_ne, half]
    ring
  change F ((t * ‖incoming‖) • polarRay width) = _
  rw [F.map_smul, terminal, Complex.real_smul, Complex.real_smul, Complex.ofReal_mul]
  have nonzero : (‖incoming‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr incoming_ne)
  field_simp

/-- The right frame's terminal ray follows the original outgoing edge, at the
same original arclength as forward time on the bank. -/
theorem radialRightCornerFrame_terminal_length (radial incoming outgoing : ℂ)
    (radial_ne : radial ≠ 0) (outgoing_ne : outgoing ≠ 0) (t : ℝ) :
    radialRightCornerFrame radial incoming
      ((t * ‖outgoing‖) • polarRay (radialRightCornerWidth radial incoming outgoing)) =
        t • outgoing := by
  simpa only [radialRightCornerFrame, radialRightCornerWidth, norm_neg, neg_neg] using
    radialLeftCornerFrame_terminal_length (-radial) (-outgoing) (-incoming)
      (neg_ne_zero.mpr radial_ne) (neg_ne_zero.mpr outgoing_ne) t

end Unfoldings
