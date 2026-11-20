module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination

/-! The outward intersection of a line and a circle is a smooth quadratic branch. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One quarter of the discriminant for the circle equation along the line `u + t • v`. -/
def circleLineDiscriminant (u v : E) (r : ℝ) : ℝ :=
  inner ℝ u v ^ 2 + ‖v‖ ^ 2 * (r ^ 2 - ‖u‖ ^ 2)

/-- The positive-radial branch of the line-circle intersection. -/
def outwardCircleLineParameter (u v : E) (r : ℝ) : ℝ :=
  (-inner ℝ u v + Real.sqrt (circleLineDiscriminant u v r)) / ‖v‖ ^ 2

theorem circleLineDiscriminant_eq {u v : E} {r t : ℝ} (on_circle : ‖u + t • v‖ = r) :
    circleLineDiscriminant u v r = inner ℝ (u + t • v) v ^ 2 := by
  have sq := congrArg (fun x : ℝ => x ^ 2) on_circle
  rw [norm_add_pow_two_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs] at sq
  rw [circleLineDiscriminant, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linear_combination -‖v‖ ^ 2 * sq

/-- Positive radial incidence selects the same branch through every transverse contact. -/
theorem outwardCircleLineParameter_eq {u v : E} {r t : ℝ}
    (on_circle : ‖u + t • v‖ = r) (outward : 0 < inner ℝ (u + t • v) v) :
    outwardCircleLineParameter u v r = t := by
  have v_ne : v ≠ 0 := by
    intro zero
    simp [zero] at outward
  rw [outwardCircleLineParameter, circleLineDiscriminant_eq on_circle,
    Real.sqrt_sq outward.le, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  apply (div_eq_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr v_ne))).mpr
  ring

/-- The root is differentiable as the supporting line moves, provided the
chosen intersection is strictly transverse. -/
theorem differentiableAt_outwardCircleLineParameter {u v : ℝ → E} {x r t : ℝ}
    (du : DifferentiableAt ℝ u x) (dv : DifferentiableAt ℝ v x)
    (on_circle : ‖u x + t • v x‖ = r) (outward : 0 < inner ℝ (u x + t • v x) (v x)) :
    DifferentiableAt ℝ (fun θ => outwardCircleLineParameter (u θ) (v θ) r) x := by
  have pd : 0 < circleLineDiscriminant (u x) (v x) r := by
    rw [circleLineDiscriminant_eq on_circle]
    exact sq_pos_of_pos outward
  have v_ne : v x ≠ 0 := by
    intro zero
    simp [zero] at outward
  have disc : DifferentiableAt ℝ (fun θ => circleLineDiscriminant (u θ) (v θ) r) x := by
    unfold circleLineDiscriminant
    exact ((du.inner ℝ dv).pow 2).add
      ((dv.norm_sq ℝ).mul ((differentiableAt_const (r ^ 2)).sub (du.norm_sq ℝ)))
  unfold outwardCircleLineParameter
  exact ((du.inner ℝ dv).neg.add (disc.sqrt pd.ne')).div (dv.norm_sq ℝ)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr v_ne))

/-- The branch lies on the requested circle whenever the discriminant is
nonnegative and the direction is nonzero. -/
theorem norm_outwardCircleLineContact {u v : E} {r : ℝ} (r_nonneg : 0 ≤ r)
    (disc : 0 ≤ circleLineDiscriminant u v r) (v_ne : v ≠ 0) :
    ‖u + outwardCircleLineParameter u v r • v‖ = r := by
  let s := outwardCircleLineParameter u v r
  let b := inner ℝ u v
  let c := ‖v‖ ^ 2
  have c_ne : c ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr v_ne)
  have formula : s * c + b = Real.sqrt (circleLineDiscriminant u v r) := by
    change ((-b + Real.sqrt (circleLineDiscriminant u v r)) / c) * c + b = _
    rw [div_mul_cancel₀ _ c_ne]
    ring
  have sq : (s * c + b) ^ 2 = b ^ 2 + c * (r ^ 2 - ‖u‖ ^ 2) := by
    rw [formula, Real.sq_sqrt disc, circleLineDiscriminant]
  change ‖u + s • v‖ = r
  apply (sq_eq_sq₀ (norm_nonneg _) r_nonneg).mp
  apply mul_left_cancel₀ c_ne
  rw [norm_add_pow_two_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change c * (‖u‖ ^ 2 + 2 * (s * b) + s ^ 2 * c) = c * r ^ 2
  linear_combination sq

end Unfoldings
