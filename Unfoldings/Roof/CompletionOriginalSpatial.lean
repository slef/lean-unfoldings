module

public import Unfoldings.Roof.CompletionOriginalConforming

/-! The physical original-piece folding commutes with every cut-metric subdivision map. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionOriginalSpatialIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Every point, with its actual original cut-side copy, has the same spatial placement. -/
theorem originalMetricEquiv_toSpace (retain : Set C.Seam)
    (x : E.originalComplex.Realization (E.originalRetain retain)) :
    (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
        (E.originalRetain retain) x =
      K.folding.toSpace retain (E.originalMetricEquiv retain x) := by
  obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective E.originalComplex.Cell
    (E.originalComplex.glue (E.originalRetain retain)) x
  change E.partition.placement i.val y.val = K.folding.place (E.originalParent i)
    (E.originalCoordinates i.val (E.originalParent i) y.val)
  exact (E.originalCoordinates_spatial i.val (E.originalParent i)
    (E.originalParent_contains i) y.val).symm

end Unfoldings.ConvexRoof.CompletionMesh
