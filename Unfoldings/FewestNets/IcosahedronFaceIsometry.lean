module

public import Unfoldings.FewestNets.IcosahedronFacets
public import Unfoldings.FewestNets.MeshFaceGeometry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Identify every icosahedral macroface with the coordinates used by the star checker. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real NormedSpace InnerProductSpace
open scoped BigOperators

/-- The common raw vertex radius used to put the icosahedron on the unit sphere. -/
def radius : ℝ := Real.sqrt (2 + goldenRatio)

theorem radius_pos : 0 < radius := Real.sqrt_pos.2 (by linarith only [goldenRatio_pos])

theorem radius_sq : radius ^ 2 = 2 + goldenRatio :=
  Real.sq_sqrt (by linarith only [goldenRatio_pos])

def unitFaceCorners (f : Fin 20) (i : Fin 3) : Space := radius⁻¹ • faceCorners f i

def modelCorners : Fin 3 → Space := ![MeshStar.cornerA, MeshStar.cornerB, MeshStar.cornerC]

private theorem ratio_eq : goldenRatio / (2 + goldenRatio) = √5 / 5 := by
  have h : 0 < 2 + goldenRatio := by linarith only [goldenRatio_pos]
  apply (div_eq_div_iff h.ne' (by norm_num)).mpr
  have sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [goldenRatio]
  linear_combination -sq / 2

private theorem inner_unitFaceCorners (f : Fin 20) (i j : Fin 3) :
    inner ℝ (unitFaceCorners f i) (unitFaceCorners f j) = if i = j then 1 else √5 / 5 := by
  have expand : inner ℝ (unitFaceCorners f i) (unitFaceCorners f j) =
      inner ℝ (faceCorners f i) (faceCorners f j) / (2 + goldenRatio) := by
    simp only [unitFaceCorners, real_inner_smul_left, real_inner_smul_right, div_eq_inv_mul]
    rw [← mul_assoc, ← pow_two, inv_pow, radius_sq, goldenRatio, div_eq_inv_mul]
  rw [expand]
  by_cases eq : i = j
  · subst j
    rw [ite_eq_left rfl, faceCorners, inner_rawVertex_self, div_self (by
      linarith only [goldenRatio_pos])]
  · rw [ite_eq_right eq, ← ratio_eq]
    congr 1
    exact inner_rawVertex_of_adjacent (adjacent_faceVertex f eq)

private theorem inner_modelCorners (i j : Fin 3) :
    inner ℝ (modelCorners i) (modelCorners j) = if i = j then 1 else √5 / 5 := by
  have ab := MeshStar.corner_pair_inner.1
  have bc := MeshStar.corner_pair_inner.2.1
  have ca := MeshStar.corner_pair_inner.2.2
  have ba := (real_inner_comm MeshStar.cornerA MeshStar.cornerB).trans ab
  have cb := (real_inner_comm MeshStar.cornerB MeshStar.cornerC).trans bc
  have ac := (real_inner_comm MeshStar.cornerC MeshStar.cornerA).trans ca
  fin_cases i <;> fin_cases j <;>
    norm_num [modelCorners, real_inner_self_eq_norm_sq, MeshStar.cornerA_unit,
      MeshStar.cornerB_unit, MeshStar.cornerC_unit, ab, bc, ca, ba, cb, ac]

private theorem linearIndependent_of_faceGram (v : Fin 3 → Space)
    (gram : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else √5 / 5) :
    LinearIndependent ℝ v := by
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
  let c : ℝ := √5 / 5
  have det : (Matrix.gram ℝ v).det = (1 - c) ^ 2 * (1 + 2 * c) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.gram_apply, gram]
    norm_num
    dsimp [c]
    ring
  have c_nonnegative : 0 ≤ c := by
    dsimp [c]
    positivity
  have c_lt : c < 1 := by
    have sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have pos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    dsimp [c]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 5)]
    nlinarith only [sq, pos]
  rw [det]
  exact (mul_pos (pow_pos (sub_pos.mpr c_lt) 2) (by linarith only [c_nonnegative])).ne'

/-- Every macroface is carried to the standard face by a linear isometry of the
unit-circumsphere coordinates, with the specified corner correspondence. -/
theorem exists_modelFace_isometry (f : Fin 20) :
    ∃ e : Space ≃ₗᵢ[ℝ] Space, ∀ i, e (modelCorners i) = unitFaceCorners f i := by
  let A := basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_of_faceGram modelCorners inner_modelCorners) (by simp [Space])
  let B := basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_of_faceGram (unitFaceCorners f) (inner_unitFaceCorners f)) (by simp [Space])
  have a (i : Fin 3) : A i = modelCorners i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  have b (i : Fin 3) : B i = unitFaceCorners f i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  let L := A.equiv B (Equiv.refl (Fin 3))
  have value (i : Fin 3) : L (modelCorners i) = unitFaceCorners f i := by
    rw [← a, ← b, Module.Basis.equiv_apply]
    rfl
  have linear (x y : Space) : inner ℝ (L x) (L y) = inner ℝ x y := by
    conv_lhs =>
      rw [← A.sum_repr x, ← A.sum_repr y]
    conv_rhs =>
      rw [← A.sum_repr x, ← A.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, a, value, inner_unitFaceCorners, inner_modelCorners]
  exact ⟨L.isometryOfInner linear, value⟩

end Unfoldings.FewestNets.Icosahedron
