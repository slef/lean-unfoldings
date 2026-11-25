module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! The principal turns at a transverse crossing combine without a full-turn ambiguity. -/

@[expose] public section

namespace Unfoldings

open Real

/-- If the incoming and outgoing closing headings are on the same strict
side of the straight bank, the two corner turns through the bank heading
sum to the closing path's principal turn. -/
theorem principal_turn_add_through_crossing {incoming bank outgoing : ℂ}
    (side : (0 < (incoming / bank).im ∧ 0 < (outgoing / bank).im) ∨
      ((incoming / bank).im < 0 ∧ (outgoing / bank).im < 0)) :
    (bank / incoming).arg + (outgoing / bank).arg = (outgoing / incoming).arg := by
  let x := incoming / bank
  let z := outgoing / bank
  have im_ne_x : x.im ≠ 0 := side.elim (fun h => h.1.ne') (fun h => h.1.ne)
  have im_ne_z : z.im ≠ 0 := side.elim (fun h => h.2.ne') (fun h => h.2.ne)
  have x_ne : x ≠ 0 := fun h => im_ne_x (congrArg Complex.im h)
  have z_ne : z ≠ 0 := fun h => im_ne_z (congrArg Complex.im h)
  have b_ne : bank ≠ 0 := (div_ne_zero_iff.mp x_ne).2
  have x_lt : x.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr im_ne_x)
  have z_lt : z.arg < π := Complex.arg_lt_pi_iff.mpr (Or.inr im_ne_z)
  have bounds : -π < z.arg - x.arg ∧ z.arg - x.arg ≤ π := by
    rcases side with positive | negative
    · have hx := Complex.arg_nonneg_iff.mpr positive.1.le
      have hz := Complex.arg_nonneg_iff.mpr positive.2.le
      constructor <;> linarith only [hx, hz, x_lt, z_lt]
    · have hx := Complex.arg_neg_iff.mpr negative.1
      have hz := Complex.arg_neg_iff.mpr negative.2
      constructor <;> linarith only [hx, hz, Complex.neg_pi_lt_arg x, Complex.neg_pi_lt_arg z]
  have closing : z / x = outgoing / incoming := div_div_div_cancel_right₀ b_ne _ _
  have turns := Complex.arg_div_coe_angle z_ne x_ne
  rw [closing, ← Real.Angle.coe_sub] at turns
  have actual := congrArg Real.Angle.toReal turns
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr bounds,
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩] at actual
  have inverse : bank / incoming = x⁻¹ := (inv_div _ _).symm
  rw [inverse, Complex.arg_inv, ite_eq_right x_lt.ne, actual]
  change -x.arg + z.arg = z.arg - x.arg
  ring

end Unfoldings
