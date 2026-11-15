module

public import Unfoldings.Geometry.OpeningSourceAngle

/-! The positive geometric angle of named bank vectors retains reentrant complementary openings. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The counterclockwise geometric opening from the first named bank to the second.
A negative principal argument denotes a genuine reentrant opening, rather than negative width. -/
def positiveGapAngle (d e : ℂ) : ℝ :=
  let angle := initialGapAngle d e
  if angle < 0 then angle + 2 * Real.pi else angle

/-- Recover the positive real heading below one full turn from the actual unit ray. -/
theorem positive_arg_polarRay {θ : ℝ} (positive : 0 < θ) (small : θ < 2 * Real.pi) :
    (if (polarRay θ).arg < 0 then (polarRay θ).arg + 2 * Real.pi else (polarRay θ).arg) = θ := by
  by_cases first_half : θ ≤ Real.pi
  · have argument : (polarRay θ).arg = θ :=
      Circle.arg_exp (by linarith [Real.pi_pos]) first_half
    rw [argument, ite_eq_right (not_lt_of_ge positive.le)]
  · have last_half : Real.pi < θ := lt_of_not_ge first_half
    have period : polarRay (θ - 2 * Real.pi) = polarRay θ := by
      simp [polarRay, Circle.exp_sub]
    have argument : (polarRay θ).arg = θ - 2 * Real.pi := by
      rw [← period]
      exact Circle.arg_exp (by linarith) (by linarith [Real.pi_pos])
    rw [argument, ite_eq_left (by linarith)]
    ring

/-- The angle is computed from actual normalized edge directions, with no aperture premise. -/
theorem positiveGapAngle_of_normalized_rotation (d e : ℂ) (genuine : d ≠ 0) {θ : ℝ}
    (positive : 0 < θ) (small : θ < 2 * Real.pi)
    (rotation : e / (‖e‖ : ℂ) = polarRay θ * (d / (‖d‖ : ℂ))) :
    positiveGapAngle d e = θ := by
  have nonzero : d / (‖d‖ : ℂ) ≠ 0 := div_ne_zero genuine
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine))
  have ratio : (e / (‖e‖ : ℂ)) / (d / (‖d‖ : ℂ)) = polarRay θ := by
    rw [rotation, mul_div_cancel_right₀ _ nonzero]
  unfold positiveGapAngle initialGapAngle
  rw [ratio]
  exact positive_arg_polarRay positive small

end Unfoldings
