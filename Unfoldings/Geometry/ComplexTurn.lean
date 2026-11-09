module

public import Unfoldings.Cone.Sector
public import Mathlib.Analysis.Complex.Angle

/-!
# A positive complex turn adds the genuine unoriented angle

Positive signed area selects the positive argument of the quotient. This
gives an exact polar successor formula with real, unreduced headings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem complex_turn_of_positive_cross {x y : ℂ}
    (positive : 0 < (starRingEnd ℂ x * y).im) :
    y = ((‖y‖ / ‖x‖ : ℝ) : ℂ) * x * polarRay (InnerProductGeometry.angle x y) := by
  have xne : x ≠ 0 := by intro zero; subst x; simp at positive
  have yne : y ≠ 0 := by intro zero; subst y; simp at positive
  have imaginary : 0 < (y / x).im := by
    rw [Complex.div_im, ← sub_div]
    have numerator : y.im * x.re - y.re * x.im = (starRingEnd ℂ x * y).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [numerator]
    exact div_pos positive (Complex.normSq_pos.mpr xne)
  have argument : (y / x).arg = InnerProductGeometry.angle x y := by
    rw [InnerProductGeometry.angle_comm x y, Complex.angle_eq_abs_arg yne xne,
      abs_of_nonneg (Complex.arg_nonneg_iff.mpr imaginary.le)]
  have polar := (Complex.norm_mul_exp_arg_mul_I (y / x)).symm
  change y / x = (‖y / x‖ : ℂ) * polarRay (y / x).arg at polar
  rw [norm_div, argument] at polar
  calc
    y = (y / x) * x := (div_mul_cancel₀ y xne).symm
    _ = _ := by rw [polar]; ring

theorem polar_successor_of_positive_cross {x y : ℂ} (θ : ℝ)
    (first : x = (‖x‖ : ℂ) * polarRay θ)
    (positive : 0 < (starRingEnd ℂ x * y).im) :
    y = (‖y‖ : ℂ) * polarRay (θ + InnerProductGeometry.angle x y) := by
  have xne : x ≠ 0 := by intro zero; subst x; simp at positive
  have cancel : ((‖y‖ / ‖x‖ : ℝ) : ℂ) * (‖x‖ : ℂ) = (‖y‖ : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr xne)]
  calc
    y = ((‖y‖ / ‖x‖ : ℝ) : ℂ) * x * polarRay (InnerProductGeometry.angle x y) :=
      complex_turn_of_positive_cross positive
    _ = ((‖y‖ / ‖x‖ : ℝ) : ℂ) * ((‖x‖ : ℂ) * polarRay θ) *
        polarRay (InnerProductGeometry.angle x y) :=
      congrArg (fun z : ℂ => ((‖y‖ / ‖x‖ : ℝ) : ℂ) * z *
        polarRay (InnerProductGeometry.angle x y)) first
    _ = _ := by rw [polarRay_add, ← mul_assoc, cancel]; ring

end Unfoldings
