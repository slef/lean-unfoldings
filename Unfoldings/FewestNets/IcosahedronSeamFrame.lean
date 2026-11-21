module

public import Unfoldings.FewestNets.IcosahedronGridPermutation
public import Unfoldings.FewestNets.MeshSeamReflection

/-! The two model faces of the reference seam map to the actual icosahedron. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real MeshStar

private theorem rawVertex_seam_opposite :
    rawVertex 8 = (goldenRatio - 1) • (rawVertex 0 + rawVertex 4) - rawVertex 2 := by
  ext i
  fin_cases i <;>
    simp [rawVertex, rawCoordinates, goldenValue, PiLp.smul_apply, PiLp.add_apply,
      PiLp.sub_apply] <;> nlinarith only [goldenRatio_sq]

/-- The corner correspondence across the reference macroedge A–B. -/
def referenceSeamOrder : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- The two original macrofaces containing the reference macroedge. -/
theorem referenceSeam_macroface_iff (f : Fin 20) :
    (0 : Fin 12) ∈ Set.range (faceVertex f) ∧ (4 : Fin 12) ∈ Set.range (faceVertex f) ↔
      f = 0 ∨ f = 2 := by
  have table : ∀ f : Fin 20,
      ((∃ i : Fin 3, faceVertex f i = 0) ∧ (∃ i : Fin 3, faceVertex f i = 4)) ↔
        f = 0 ∨ f = 2 := by decide +kernel
  exact table f

theorem exists_referenceSeam_frame :
    ∃ L : Space ≃ₗᵢ[ℝ] Space,
      (∀ j, L (modelCorners j) = unitFaceCorners 0 j) ∧
      (∀ j, (seamReflection.trans L) (modelCorners j) =
        unitFaceCorners 2 (referenceSeamOrder j)) := by
  obtain ⟨L, model⟩ := exists_modelFace_isometry 0
  have a : L cornerA = radius⁻¹ • rawVertex 0 := model 0
  have b : L cornerB = radius⁻¹ • rawVertex 4 := model 1
  have c : L cornerC = radius⁻¹ • rawVertex 2 := model 2
  refine ⟨L, model, fun j => ?_⟩
  fin_cases j
  · change L (seamReflection cornerA) = radius⁻¹ • rawVertex 0
    rw [seamReflection_cornerA, a]
  · change L (seamReflection cornerB) = radius⁻¹ • rawVertex 4
    rw [seamReflection_cornerB, b]
  · change L (seamReflection cornerC) = radius⁻¹ • rawVertex 8
    rw [seamReflection_cornerC, map_sub, map_smul, map_add, a, b, c, rawVertex_seam_opposite]
    module

end Unfoldings.FewestNets.Icosahedron
