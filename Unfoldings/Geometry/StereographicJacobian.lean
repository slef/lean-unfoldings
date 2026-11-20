module

public import Unfoldings.Geometry.StereographicHemisphere
public import Unfoldings.Cap.VerticalProduct
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The radial extension of the stereographic chart has an exact spatial Jacobian. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- A planar chart point and a radial parameter are stored as spatial coordinates. -/
def radialStereographic (z : Space) : Space := z 2 • inverseStereographic (horizontal z)

/-- The numerator of the inverse chart at the horizontal coordinates. -/
def stereographicNumerator (z : Space) : Space :=
  (2 : ℝ) • horizontalLift (horizontal z) + (1 - ‖horizontal z‖ ^ 2) • northLift 0

/-- Differential of the squared horizontal norm in spatial coordinates. -/
def horizontalNormSqDerivative (z : Space) : Space →L[ℝ] ℝ :=
  2 • (innerSL ℝ (horizontal z)).comp horizontalCLM

/-- Differential of the inverse chart's numerator. -/
def stereographicNumeratorDerivative (z : Space) : Space →L[ℝ] Space :=
  (2 : ℝ) • (horizontalLiftIsometry.toContinuousLinearMap.comp horizontalCLM) -
    (horizontalNormSqDerivative z).smulRight (northLift 0)

/-- Differential of the common scalar factor in the radial chart. -/
def radialStereographicFactorDerivative (z : Space) : Space →L[ℝ] ℝ :=
  z 2 • ((ContinuousLinearMap.toSpanSingleton ℝ
    (-((1 + ‖horizontal z‖ ^ 2) ^ 2)⁻¹)).comp (horizontalNormSqDerivative z)) +
    (1 + ‖horizontal z‖ ^ 2)⁻¹ • EuclideanSpace.proj 2

def radialStereographicDerivative (z : Space) : Space →L[ℝ] Space :=
  (z 2 * (1 + ‖horizontal z‖ ^ 2)⁻¹) • stereographicNumeratorDerivative z +
    (radialStereographicFactorDerivative z).smulRight (stereographicNumerator z)

theorem hasFDerivAt_radialStereographic (z : Space) :
    HasFDerivAt radialStereographic (radialStereographicDerivative z) z := by
  have nsq : HasFDerivAt (fun w : Space => ‖horizontal w‖ ^ 2)
      (horizontalNormSqDerivative z) z := horizontalCLM.hasFDerivAt.norm_sq
  have den : HasFDerivAt (fun w : Space => 1 + ‖horizontal w‖ ^ 2)
      (horizontalNormSqDerivative z) z := by
    have h := (hasFDerivAt_const (1 : ℝ) z).add nsq
    rw [zero_add] at h
    exact h
  have frac := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).hasFDerivAt.mul
    ((hasFDerivAt_inv (show 1 + ‖horizontal z‖ ^ 2 ≠ 0 by positivity)).comp z den)
  have lift := ((horizontalLiftIsometry.toContinuousLinearMap).comp horizontalCLM).hasFDerivAt
    (x := z)
  have upper : HasFDerivAt (fun w : Space => (1 - ‖horizontal w‖ ^ 2))
      (-horizontalNormSqDerivative z) z := by
    have h := (hasFDerivAt_const (1 : ℝ) z).sub nsq
    rw [zero_sub] at h
    exact h
  have num : HasFDerivAt stereographicNumerator (stereographicNumeratorDerivative z) z := by
    have combined := (lift.const_smul (2 : ℝ)).add (upper.smul_const (northLift 0))
    have eq : stereographicNumeratorDerivative z =
        (2 : ℝ) • (horizontalLiftIsometry.toContinuousLinearMap.comp horizontalCLM) +
          (-horizontalNormSqDerivative z).smulRight (northLift 0) := by
      ext w i
      simp [stereographicNumeratorDerivative, sub_eq_add_neg]
    rw [eq]
    exact combined
  have derivative := frac.smul num
  have eqfun : radialStereographic =
      fun w : Space => (w 2 * (1 + ‖horizontal w‖ ^ 2)⁻¹) • stereographicNumerator w := by
    funext w
    simp only [radialStereographic, inverseStereographic, stereographicNumerator,
      smul_add, smul_smul, div_eq_mul_inv]
    congr 2 <;> ring
  rw [eqfun]
  exact derivative

/-- The spatial Jacobian equals the spherical area density times the squared radial parameter. -/
theorem det_radialStereographicDerivative (z : Space) :
    (radialStereographicDerivative z).det = 4 * (z 2) ^ 2 / (1 + ‖horizontal z‖ ^ 2) ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have normsq : ‖horizontal z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  have den : 1 + (z 0) ^ 2 + (z 1) ^ 2 ≠ 0 := by positivity
  change LinearMap.det (radialStereographicDerivative z).toLinearMap = _
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_three]
  simp [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply, radialStereographicDerivative,
    radialStereographicFactorDerivative, stereographicNumeratorDerivative, stereographicNumerator,
    horizontalNormSqDerivative, ContinuousLinearMap.toSpanSingleton_apply, horizontalCLM,
    horizontalLiftIsometry, horizontalLift, northLift, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, EuclideanSpace.single, PiLp.single_apply, normsq, ← add_assoc]
  field_simp [den]
  ring

end Unfoldings.Cap
