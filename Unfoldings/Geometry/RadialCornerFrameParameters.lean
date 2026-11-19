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

end Unfoldings
