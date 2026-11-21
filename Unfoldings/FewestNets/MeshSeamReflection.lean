module

public import Unfoldings.FewestNets.MeshChartFrame
public import Unfoldings.FewestNets.MeshFaceGeometry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.NumberTheory.Real.GoldenRatio

/-! The reflected model face describes the second triangle at a macroedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open Real NormedSpace
open scoped BigOperators

def seamAxis : Space := normalize (spatialCross cornerA cornerB)

private theorem seamAxis_unit : ‖seamAxis‖ = 1 := by
  have cross_ne : spatialCross cornerA cornerB ≠ 0 := by
    intro zero
    have sq := norm_sq_spatialCross cornerA cornerB
    rw [zero, norm_zero, cornerA_unit, cornerB_unit, corner_pair_inner.1] at sq
    nlinarith only [sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  exact norm_normalize cross_ne

private theorem inner_cornerA_seamAxis : inner ℝ cornerA seamAxis = 0 := by
  rw [seamAxis, NormedSpace.normalize, real_inner_smul_right, inner_left_spatialCross, mul_zero]

private theorem inner_cornerB_seamAxis : inner ℝ cornerB seamAxis = 0 := by
  rw [seamAxis, NormedSpace.normalize, real_inner_smul_right, inner_right_spatialCross, mul_zero]

/-- The macroedge reflection is a linear isometry. -/
def seamReflection : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ seamAxis)ᗮ.reflection

theorem seamReflection_apply (x : Space) : seamReflection x = reflectAB x := by
  rw [seamReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, seamAxis_unit]
  change -(2 • (inner ℝ seamAxis x / (1 : ℝ) ^ 2) • seamAxis - x) =
    x - (2 * inner ℝ x seamAxis) • seamAxis
  rw [one_pow, div_one, real_inner_comm x seamAxis, two_smul ℕ, ← add_smul, ← two_mul, neg_sub]

@[simp] theorem seamReflection_cornerA : seamReflection cornerA = cornerA := by
  rw [seamReflection_apply]
  change cornerA - (2 * inner ℝ cornerA seamAxis) • seamAxis = cornerA
  rw [inner_cornerA_seamAxis, mul_zero, zero_smul, sub_zero]

@[simp] theorem seamReflection_cornerB : seamReflection cornerB = cornerB := by
  rw [seamReflection_apply]
  change cornerB - (2 * inner ℝ cornerB seamAxis) • seamAxis = cornerB
  rw [inner_cornerB_seamAxis, mul_zero, zero_smul, sub_zero]

private theorem linearIndependent_seamVectors :
    LinearIndependent ℝ (![cornerA, cornerB, seamAxis] : Fin 3 → Space) := by
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
  have ab := corner_pair_inner.1
  have ba := (real_inner_comm cornerA cornerB).trans ab
  have a := inner_cornerA_seamAxis
  have b := inner_cornerB_seamAxis
  have ar := (real_inner_comm cornerA seamAxis).trans a
  have br := (real_inner_comm cornerB seamAxis).trans b
  rw [Matrix.det_fin_three]
  simp [Matrix.gram_apply, ab, ba, a, b, ar, br, cornerA_unit,
    cornerB_unit, seamAxis_unit]
  have sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith only [sq]

/-- The third vertex across the seam is an exact combination of the original three. -/
theorem seamReflection_cornerC :
    seamReflection cornerC = (goldenRatio - 1) • (cornerA + cornerB) - cornerC := by
  let v : Fin 3 → Space := ![cornerA, cornerB, seamAxis]
  let B := basisOfLinearIndependentOfCardEqFinrank linearIndependent_seamVectors (by simp [Space])
  have basis (i : Fin 3) : B i = v i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i
  let d := (goldenRatio - 1) • (cornerA + cornerB) - cornerC
  have ac := (real_inner_comm cornerC cornerA).trans corner_pair_inner.2.2
  have bc := corner_pair_inner.2.1
  have ab := corner_pair_inner.1
  have ba := (real_inner_comm cornerA cornerB).trans ab
  have formula : (goldenRatio - 1) * (1 + √5 / 5) = 2 * (√5 / 5) := by
    unfold goldenRatio
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have a : inner ℝ cornerA d = inner ℝ cornerA cornerC := by
    dsimp only [d]
    rw [inner_sub_right, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
      cornerA_unit, one_pow, ab, ac, formula]
    ring
  have b : inner ℝ cornerB d = inner ℝ cornerB cornerC := by
    dsimp only [d]
    rw [inner_sub_right, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
      cornerB_unit, one_pow, ba, bc, add_comm (√5 / 5) 1, formula]
    ring
  have along : inner ℝ seamAxis d = -inner ℝ seamAxis cornerC := by
    dsimp only [d]
    rw [inner_sub_right, real_inner_smul_right, inner_add_right,
      (real_inner_comm cornerA seamAxis).trans inner_cornerA_seamAxis,
      (real_inner_comm cornerB seamAxis).trans inner_cornerB_seamAxis,
      zero_add, mul_zero, zero_sub]
  have pair (i : Fin 3) : inner ℝ (v i) (seamReflection cornerC) = inner ℝ (v i) d := by
    fin_cases i
    · change inner ℝ cornerA (seamReflection cornerC) = _
      have preserve := seamReflection.inner_map_map cornerA cornerC
      rw [seamReflection_cornerA] at preserve
      exact preserve.trans a.symm
    · change inner ℝ cornerB (seamReflection cornerC) = _
      have preserve := seamReflection.inner_map_map cornerB cornerC
      rw [seamReflection_cornerB] at preserve
      exact preserve.trans b.symm
    · change inner ℝ seamAxis (seamReflection cornerC) = inner ℝ seamAxis d
      rw [along, seamReflection_apply]
      change inner ℝ seamAxis (cornerC - (2 * inner ℝ cornerC seamAxis) • seamAxis) = _
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        seamAxis_unit, one_pow, mul_one, real_inner_comm seamAxis cornerC]
      ring
  change seamReflection cornerC = d
  apply ext_inner_left ℝ
  intro z
  rw [← B.sum_repr z]
  simp only [sum_inner, real_inner_smul_left, basis, pair]

end Unfoldings.FewestNets.MeshStar
