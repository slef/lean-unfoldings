module

public import Unfoldings.Geometry.ComplexArea

/-! Reflection in the horizontal coordinate axis as a linear planar isometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def planeConjugation : Plane ≃ₗᵢ[ℝ] Plane :=
  (Complex.orthonormalBasisOneI.repr.symm.trans Complex.conjLIE).trans
    Complex.orthonormalBasisOneI.repr

theorem planeConjugation_apply (z : Plane) :
    planeConjugation z = WithLp.toLp 2 ![z 0, -z 1] := by
  change Complex.orthonormalBasisOneI.repr
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm z)) = _
  apply WithLp.ofLp_injective 2
  rw [Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]
  ext i
  fin_cases i <;> simp

@[simp] theorem orient_planeConjugation (x y : Plane) :
    orient 0 (planeConjugation x) (planeConjugation y) = -orient 0 x y := by
  rw [planeConjugation_apply, planeConjugation_apply]
  simp [orient]
  ring

end Unfoldings
