module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! The vertical primitive of the solid-angle density in gnomonic coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

/-- In the chart with first coordinate `p`, this primitive integrates the
solid-angle density in the second coordinate. -/
def gnomonicAreaPrimitive (p q : ℝ) : ℝ :=
  q / ((1 + p ^ 2) * √(1 + p ^ 2 + q ^ 2))

theorem hasDerivAt_gnomonicAreaPrimitive (p q : ℝ) :
    HasDerivAt (gnomonicAreaPrimitive p) (1 / (√(1 + p ^ 2 + q ^ 2)) ^ 3) q := by
  let c := 1 + p ^ 2
  let d := √(c + q ^ 2)
  have cpos : 0 < c := by dsimp only [c]; positivity
  have sum_pos : 0 < c + q ^ 2 := add_pos_of_pos_of_nonneg cpos (sq_nonneg q)
  have dpos : 0 < d := Real.sqrt_pos.mpr sum_pos
  have dsq : d ^ 2 = c + q ^ 2 := Real.sq_sqrt sum_pos.le
  have inner : HasDerivAt (fun t : ℝ => c + t ^ 2) (2 * q) q := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hasDerivAt_pow 2 q).const_add c
  have denom : HasDerivAt (fun t : ℝ => c * √(c + t ^ 2)) (c * ((2 * q) / (2 * d))) q :=
    HasDerivAt.const_mul c (inner.sqrt sum_pos.ne')
  have deriv := HasDerivAt.fun_div (hasDerivAt_id q) denom (mul_ne_zero cpos.ne' dpos.ne')
  convert deriv using 1 <;> try rfl
  change 1 / d ^ 3 = (1 * (c * d) - q * (c * ((2 * q) / (2 * d)))) / (c * d) ^ 2
  field_simp [dpos.ne', cpos.ne']
  linear_combination -dsq

/-- The exact solid-angle density of a vertical gnomonic interval integrates to
the difference of its upper and lower primitives. -/
theorem integral_gnomonicArea_vertical (p lo hi : ℝ) :
    (∫ q in lo..hi, 1 / (√(1 + p ^ 2 + q ^ 2)) ^ 3) =
      gnomonicAreaPrimitive p hi - gnomonicAreaPrimitive p lo := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro q _
    exact hasDerivAt_gnomonicAreaPrimitive p q
  · apply Continuous.intervalIntegrable
    apply continuous_const.div (Continuous.pow (Real.continuous_sqrt.comp (by fun_prop)) _)
    intro q
    exact pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'

end Unfoldings
