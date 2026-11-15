module

public import Unfoldings.Geometry.PositiveGapAngle

/-! A common actual plane rotation preserves the positive named-bank aperture. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Common nonzero complex scaling preserves the positive aperture, including zero bank
vectors and reentrant angles. Translation cancels in the original edge differences. -/
theorem positiveGapAngle_mul_left (a d e : ℂ) (nonzero : a ≠ 0) :
    positiveGapAngle (a * d) (a * e) = positiveGapAngle d e := by
  have unit_nonzero : a / (‖a‖ : ℂ) ≠ 0 :=
    div_ne_zero nonzero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))
  have normalized (z : ℂ) : (a * z) / (‖a * z‖ : ℂ) =
      (a / (‖a‖ : ℂ)) * (z / (‖z‖ : ℂ)) := by
    rw [norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  unfold positiveGapAngle initialGapAngle
  rw [normalized, normalized, mul_div_mul_left _ _ unit_nonzero]

end Unfoldings
