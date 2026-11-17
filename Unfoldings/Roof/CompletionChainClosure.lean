module

public import Unfoldings.Roof.CompletionChainProjectedParameters
public import Unfoldings.Roof.CompletionChainSpatialTrace
public import Unfoldings.Geometry.PolygonalClosureEquations

/-! Physical cap subdivision retains the whole original geometric Jordan closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainClosureIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

local notation "F" => E.partition.pairedFolding.restrictFaces E.originalPieceSet

open Classical in
/-- The completed cap projects the entire original actual bank carrier exactly. -/
theorem cap_projected_path_range :
    Set.range (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).path =
      Set.range (K.folding.projectedBoundaryChain coarse).path :=
  (congrArg (fun P : PolygonalChain Plane (R.length + 1) => Set.range P.path)
    R.cap_projectedBoundaryChain_eq).trans
    (((F).projectedBoundaryChain_path_range R.chain).trans
      (R.projected_trace_image.trans (K.folding.projectedBoundaryChain_path_range coarse).symm))

open Classical in
/-- Cap normalization and subdivision retain the exact original projected initial point. -/
theorem cap_projected_initial :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).vertex 0 =
      (K.folding.projectedBoundaryChain coarse).vertex 0 := by
  have spatial := (E.originalMetricEquiv_toSpace retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain) R.chain.first))).trans
    (congrArg (K.folding.toSpace retain) R.first_image)
  exact (congrArg (fun P : PolygonalChain Plane (R.length + 1) => P.vertex 0)
    R.cap_projectedBoundaryChain_eq).trans
    (((F).projectedBoundaryChain_vertex_castSucc R.chain 0).trans
      ((congrArg Cap.horizontal spatial).trans
        (K.folding.projectedBoundaryChain_vertex_castSucc coarse 0).symm))

open Classical in
/-- The true terminal bank endpoint keeps its original projected position. -/
theorem cap_projected_terminal :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).vertex (Fin.last (R.length + 1)) =
      (K.folding.projectedBoundaryChain coarse).vertex (Fin.last (n + 1)) := by
  have spatial := (E.originalMetricEquiv_toSpace retain
    (E.originalComplex.vertexPoint (E.originalRetain retain)
      (E.originalComplex.boundaryEndVertex (E.originalRetain retain)
        (E.originalComplex.boundaryTurn (E.originalRetain retain) R.chain.last)))).trans
    (congrArg (K.folding.toSpace retain) R.last_image)
  exact (congrArg (fun P : PolygonalChain Plane (R.length + 1) =>
    P.vertex (Fin.last (R.length + 1))) R.cap_projectedBoundaryChain_eq).trans
    (((F).projectedBoundaryChain_vertex_last R.chain).trans
      ((congrArg Cap.horizontal spatial).trans
        (K.folding.projectedBoundaryChain_vertex_last coarse).symm))

open Classical in
/-- The comparison closure is unchanged as a geometric curve, despite all inserted vertices. -/
theorem cap_projected_closure (source closing : Plane) :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).threeSegmentClosure source closing =
      (K.folding.projectedBoundaryChain coarse).threeSegmentClosure source closing := by
  unfold PolygonalChain.threeSegmentClosure
  rw [R.cap_projected_path_range, R.cap_projected_initial, R.cap_projected_terminal]

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
