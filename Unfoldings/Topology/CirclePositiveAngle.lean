module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Order.IntermediateValue

/-! Positive real angular coordinates on the circle punctured at one. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The branch in `(0, 2π]`, with its cut at one. -/
def circlePositiveAngle (z : Circle) : ℝ := Real.pi + Complex.arg (-z : Circle)

private theorem circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

@[simp] theorem circle_exp_positiveAngle (z : Circle) :
    Circle.exp (circlePositiveAngle z) = z := by
  rw [circlePositiveAngle, Circle.exp_add, circle_exp_pi, Circle.exp_arg]
  apply Subtype.ext
  simp

@[simp] theorem circlePositiveAngle_exp {θ : ℝ} (positive : 0 < θ)
    (short : θ < 2 * Real.pi) : circlePositiveAngle (Circle.exp θ) = θ := by
  have minus : -Circle.exp θ = Circle.exp (θ - Real.pi) := by
    rw [Circle.exp_sub, circle_exp_pi]
    apply Subtype.ext
    simp only [Circle.coe_neg, div_neg, div_one]
  rw [circlePositiveAngle, minus, Circle.arg_exp (by linarith) (by linarith)]
  ring

theorem circlePositiveAngle_pos (z : Circle) : 0 < circlePositiveAngle z := by
  have bound := Complex.neg_pi_lt_arg (-z : Circle)
  dsimp only [circlePositiveAngle]
  linarith

theorem circlePositiveAngle_lt_two_pi {z : Circle} (different : z ≠ 1) :
    circlePositiveAngle z < 2 * Real.pi := by
  have unequal : Complex.arg (-z : Circle) ≠ Real.pi := by
    intro equal
    have same : (-z : Circle) = -1 := Circle.injective_arg (by simpa using equal)
    exact different (neg_injective same)
  have bound := (Complex.arg_le_pi (-z : Circle)).lt_of_ne unequal
  dsimp only [circlePositiveAngle]
  linarith

theorem circlePositiveAngle_injective : Function.Injective circlePositiveAngle := by
  intro z w equal
  exact neg_injective (Circle.injective_arg (add_left_cancel equal))

/-- The cut is at one; the negative real axis is a regular point of this coordinate. -/
theorem continuousOn_circlePositiveAngle :
    ContinuousOn circlePositiveAngle {z : Circle | z ≠ 1} := by
  intro z different
  have slit : (-z : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    refine ⟨?_, neg_ne_zero.mpr z.coe_ne_zero⟩
    intro equal
    have same : (-z : Circle) = -1 := Circle.injective_arg (by simpa using equal)
    exact different (neg_injective same)
  have continuous_neg : Continuous (fun w : Circle => -(w : ℂ)) := continuous_subtype_val.neg
  have regular : ContinuousAt (fun w : Circle => Complex.arg (-(w : ℂ))) z :=
    (Complex.continuousAt_arg slit).comp (f := fun w : Circle => -(w : ℂ))
      continuous_neg.continuousAt
  exact (continuous_const.continuousAt.add regular).continuousWithinAt

theorem continuousAt_circlePositiveAngle {z : Circle} (different : z ≠ 1) :
    ContinuousAt circlePositiveAngle z :=
  (continuousOn_circlePositiveAngle z different).continuousAt
    (isOpen_ne.mem_nhds different)

/-- An explicit homeomorphism, without selecting a covering-space lift. -/
def circlePositiveAngleHomeomorph : {z : Circle // z ≠ 1} ≃ₜ Set.Ioo 0 (2 * Real.pi) where
  toFun z := ⟨circlePositiveAngle z.val, circlePositiveAngle_pos _,
    circlePositiveAngle_lt_two_pi z.property⟩
  invFun θ := ⟨Circle.exp θ.val, by
    intro equal
    have angle := circlePositiveAngle_exp θ.property.1 θ.property.2
    rw [equal] at angle
    have at_one : circlePositiveAngle 1 = 2 * Real.pi := by
      simp [circlePositiveAngle]
      ring
    rw [at_one] at angle
    exact θ.property.2.ne angle.symm⟩
  left_inv z := Subtype.ext (circle_exp_positiveAngle z.val)
  right_inv θ := Subtype.ext (circlePositiveAngle_exp θ.property.1 θ.property.2)
  continuous_toFun :=
    (continuousOn_circlePositiveAngle.domRestrict).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Circle.exp.continuous.comp continuous_subtype_val

end Unfoldings
