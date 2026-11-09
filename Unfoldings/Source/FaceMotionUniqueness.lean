module

public import Unfoldings.Source.FaceAtlas

/-! Any actual local expression of source coordinates determines the selected face motion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceFaceMotion_eq_of_patch :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      (x : P.sourceFaceRegion source f) (A : Plane ≃ᵃⁱ[ℝ] Plane) {r : ℝ}, 0 < r →
      (∀ y : C.Cell f, dist y.val x.val.val < r →
        ∃ outside : C.faceMap Set.univ f y ∉ sourceCutLocus source,
          P.sourceFaceCoordinates R f ⟨y, outside⟩ = A y.val) →
      P.sourceFaceMotion R f x = A := by
  let := P.metricSpace
  intro source R f x A r positive agrees
  let patch := P.sourceFacePatch R f x
  apply rigid_eq_on_convex_patch (C.triangle f).convex_carrier
    (C.triangle f).interior_nonempty x.val.property (lt_min positive patch.positive)
  intro z member close
  let y : C.Cell f := ⟨z, member⟩
  obtain ⟨outside, equal⟩ := agrees y (close.trans_le (min_le_left _ _))
  have selected := patch.agrees ⟨y, outside⟩ (close.trans_le (min_le_right _ _))
  exact selected.symm.trans equal

end Unfoldings.SpatialFolding.ConvexBoundary
