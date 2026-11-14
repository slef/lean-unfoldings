module

public import Unfoldings.Geometry.SegmentEquation
public import Unfoldings.Geometry.ComplexArea

/-! Proper affine equations for whole complex lines, including degenerate segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def complexLineEquation (a b : ℂ) : ℂ →ᵃ[ℝ] ℝ :=
  (segmentEquation (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr b)).comp
    Complex.orthonormalBasisOneI.repr.toAffineMap

theorem complexLineEquation_ne_zero (a b : ℂ) : complexLineEquation a b ≠ 0 := by
  intro zero
  apply segmentEquation_ne_zero (Complex.orthonormalBasisOneI.repr a)
    (Complex.orthonormalBasisOneI.repr b)
  ext x
  have equality := congrArg (fun l : ℂ →ᵃ[ℝ] ℝ =>
    l (Complex.orthonormalBasisOneI.repr.symm x)) zero
  change segmentEquation (Complex.orthonormalBasisOneI.repr a)
    (Complex.orthonormalBasisOneI.repr b)
      (Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI.repr.symm x)) = 0 at equality
  rw [LinearIsometryEquiv.apply_symm_apply] at equality
  exact equality

@[simp] theorem complexLineEquation_first (a b : ℂ) : complexLineEquation a b a = 0 :=
  segmentEquation_eq_zero (left_mem_segment ℝ _ _)

@[simp] theorem complexLineEquation_last (a b : ℂ) : complexLineEquation a b b = 0 :=
  segmentEquation_eq_zero (right_mem_segment ℝ _ _)

/-- The equation holds on the whole supporting line, including both unbounded tails. -/
theorem complexLineEquation_lineMap (a b : ℂ) (t : ℝ) :
    complexLineEquation a b (AffineMap.lineMap a b t) = 0 := by
  rw [(complexLineEquation a b).apply_lineMap, complexLineEquation_first,
    complexLineEquation_last, AffineMap.lineMap_same, AffineMap.const_apply]

end Unfoldings
