module

public import Unfoldings.Cap.GermVectors
public import Unfoldings.Complex.RootwardParentChain

/-! Actual current rootward banks project onto the original parent segments point for point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The actual folded position of a bank end is its original projected vertex position. -/
theorem projected_boundaryPosition {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    Cap.horizontal (K.folding.boundaryPosition p) =
      K.projectedVertex
        (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p)) := by
  rw [projectedVertex, C.vertexPoint_vertexForgetCuts, K.folding.toSpace_forgetCuts]
  rfl

/-- Every bank parameter is preserved, including both endpoints and every strict interior point. -/
theorem projected_directedBoundaryPath {retain : Set C.Seam} (p : C.BoundaryEnd retain)
    (t : unitInterval) :
    Cap.horizontal (K.folding.toSpace retain (C.directedBoundaryPath p t)) =
      AffineMap.lineMap
        (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p)))
        (K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex retain (C.boundaryTurn retain p)))) t.val := by
  rw [K.folding.directedBoundaryPath_position, K.folding.germDirection_boundary_positions]
  change Cap.horizontalCLM (_ + t.val • (_ - _)) = _
  have projected (q : C.BoundaryEnd retain) : Cap.horizontalCLM (K.folding.boundaryPosition q) =
      K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain q)) :=
    K.projected_boundaryPosition q
  rw [map_add, map_smul, map_sub, projected p, projected (C.boundaryTurn retain p),
    AffineMap.lineMap_apply_module']
  exact add_comm _ _

variable {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))

include roots starts in
/-- The actual upcoming bank is the complete original rootward parent segment. -/
theorem rootward_projected_bank (j : C.RootwardBank S Q i) (t : unitInterval) :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    Cap.horizontal (K.folding.toSpace retain (C.directedBoundaryPath
      (C.survivingBoundaryEnd (Q.cycle.point j.val) j.property.2.1) t)) =
      AffineMap.lineMap (K.projectedVertex (C.contourOriginalVertex S Q j.val))
        (K.projectedVertex (P.parent (C.contourOriginalVertex S Q j.val))) t.val := by
  have data := C.future_current_bank_rootward S roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  dsimp only
  rw [K.projected_directedBoundaryPath]
  congr 2
  exact congrArg K.projectedVertex data.2.2.2

variable (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)
  (m : ℕ) (length : P.distanceToRoot (C.contourOriginalVertex S Q i) = m + 2)

/-- The geometric reference path uses the original parent vertices, including its rim root. -/
def rootwardProjectedParentChain : PolygonalChain Plane (m + 1) where
  vertex k := K.projectedVertex (P.parent^[k.val + 1] (C.contourOriginalVertex S Q i))

include roots starts in
/-- Identify the constructed intrinsic bank chain with its original projected segments
throughout every edge; the actual current endpoint-copy choices are already derived. -/
theorem rootwardProjectedParentChain_point (k : Fin (m + 1)) (t : unitInterval) :
    let retain := C.processedParentRetain S (C.contourFrontier S Q i)
    Cap.horizontal (K.folding.toSpace retain (C.directedBoundaryPath
      ((K.folding.rootwardParentBankChain S roots Q starts i single m length).point k) t)) =
        (K.rootwardProjectedParentChain S Q i m).point k t := by
  have bank := K.rootward_projected_bank S roots Q starts i
    (SpatialFolding.rootwardParentBank S roots Q starts i single m length k) t
  rw [SpatialFolding.rootwardParentBank_original] at bank
  change _ = AffineMap.lineMap
    (K.projectedVertex (P.parent^[k.val + 1] (C.contourOriginalVertex S Q i)))
    (K.projectedVertex (P.parent^[k.val + 1 + 1] (C.contourOriginalVertex S Q i))) t.val
  simpa only [Function.iterate_succ_apply'] using! bank

include length in
/-- The physical projected original vertices never repeat before the first rim root. -/
theorem rootwardProjectedParentChain_vertex_injective :
    Function.Injective (K.rootwardProjectedParentChain S Q i m).vertex := by
  intro a b same
  have vertices := K.projectedVertex_injective same
  let a' : Fin (P.distanceToRoot (C.contourOriginalVertex S Q i) + 1) :=
    ⟨a.val + 1, by rw [length]; omega⟩
  let b' : Fin (P.distanceToRoot (C.contourOriginalVertex S Q i) + 1) :=
    ⟨b.val + 1, by rw [length]; omega⟩
  have equal : a' = b' := (P.strictMono_height_rootOrbit (C.contourOriginalVertex S Q i)).injective
    (congrArg P.height vertices)
  have values := congrArg (fun k : Fin (P.distanceToRoot (C.contourOriginalVertex S Q i) + 1) =>
    k.val) equal
  apply Fin.ext
  dsimp only [a', b'] at values
  omega

end Unfoldings.ConvexCap
