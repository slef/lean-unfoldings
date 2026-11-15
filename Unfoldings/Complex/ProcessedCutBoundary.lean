module

public import Unfoldings.Complex.ProcessedCutForest
public import Unfoldings.Complex.InteriorCopyAngles

/-! The boundary copies of every intermediate original cut are exactly its processed vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier) (roots : P.roots = C.relativeCutRoots Set.univ)

include roots in
/-- Every actual copy above a processed original vertex lies on the intermediate cut boundary. -/
theorem processedCut_boundary_of_processed
    (w : C.Vertex (C.processedParentRetain S frontier))
    (processed : C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed) :
    C.IsBoundaryVertex (C.processedParentRetain S frontier) w := by
  let inclusion := Set.subset_univ (C.processedParentRetain S frontier)
  let v := C.vertexForgetCuts inclusion w
  apply (C.vertexPoint_mem_bankBoundary_iff (C.processedParentRetain S frontier) w).mp
  by_cases root : v ∈ P.roots
  · apply C.bankBoundary_preimage_forgetCuts inclusion
    change C.forgetCuts inclusion (C.vertexPoint (C.processedParentRetain S frontier) w) ∈
      C.bankBoundary Set.univ
    rw [← C.vertexPoint_vertexForgetCuts]
    have boundary := root
    rw [roots] at boundary
    exact (C.vertexPoint_mem_bankBoundary_iff Set.univ v).mpr boundary
  · let a : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨v, root⟩
    let s := S.edge a
    have cut : s ∉ C.processedParentRetain S frontier :=
      (C.not_mem_processedParentRetain_iff S frontier s).mpr ⟨a, processed, rfl⟩
    have endpoint_boundary (b : Bool) (endpoint : v = C.seamVertex s b) :
        C.vertexPoint (C.processedParentRetain S frontier) w ∈
          C.bankBoundary (C.processedParentRetain S frontier) := by
      let y := C.vertexOfCorner (C.processedParentRetain S frontier)
        (C.germOfEndpoint (C.left s) b).1
      have boundary : C.IsBoundaryVertex (C.processedParentRetain S frontier) y := by
        cases b
        · exact C.bank_start_isBoundaryVertex _ (C.leftBank _ s cut)
        · exact C.bank_finish_isBoundaryVertex _ (C.leftBank _ s cut)
      have original : C.vertexForgetCuts inclusion y = v := by
        change C.vertexForgetCuts inclusion
          (C.vertexOfCorner (C.processedParentRetain S frontier)
            (C.germOfEndpoint (C.left s) b).1) = v
        rw [C.vertexForgetCuts_vertexOfCorner]
        exact endpoint.symm
      have equal : C.forgetCuts inclusion (C.vertexPoint (C.processedParentRetain S frontier) y) =
          C.forgetCuts inclusion (C.vertexPoint (C.processedParentRetain S frontier) w) := by
        rw [← C.vertexPoint_vertexForgetCuts, ← C.vertexPoint_vertexForgetCuts, original]
      have present :=
        (C.vertexPoint_mem_bankBoundary_iff (C.processedParentRetain S frontier) y).mpr boundary
      rcases C.forgetCuts_fiber_eq_or_boundary inclusion _ _ equal with same | both
      · exact same ▸ present
      · exact both.2
    have link := S.link a
    rcases link with first | last
    · exact endpoint_boundary false first.1
    · exact endpoint_boundary true last.1

include roots in
/-- Intermediate boundary copies correspond exactly to the processed original vertex set. -/
theorem processedCut_isBoundaryVertex_iff
    (w : C.Vertex (C.processedParentRetain S frontier)) :
    C.IsBoundaryVertex (C.processedParentRetain S frontier) w ↔
      C.vertexForgetCuts (Set.subset_univ _) w ∈ frontier.processed := by
  constructor
  · intro boundary
    let retain := C.processedParentRetain S frontier
    have member := C.relativeBoundaryVertex_member (Set.subset_univ retain)
      (⟨w, boundary⟩ : C.BoundaryVertex retain)
    exact (C.processedCut_vertex_mem_iff S frontier roots _).mp member
  · exact C.processedCut_boundary_of_processed S frontier roots w

include roots in
/-- Unprocessed original vertices retain their actual whole corner angle at intermediate stages. -/
theorem processedCut_totalAngle_at_unprocessed
    (w : C.Vertex (C.processedParentRetain S frontier))
    (fresh : C.vertexForgetCuts (Set.subset_univ _) w ∉ frontier.processed) :
    C.totalAngle (C.processedParentRetain S frontier) w =
      C.totalAngle Set.univ (C.vertexForgetCuts (Set.subset_univ _) w) :=
  C.totalAngle_eq_of_internal_copy (Set.subset_univ _) w
    (fun boundary => fresh ((C.processedCut_isBoundaryVertex_iff S frontier roots w).mp boundary))

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ) (frontier : P.ParentFrontier)

/-- An actual covering cyclic order for the banks of the intermediate intrinsic cut disk. -/
def processedParentBoundaryContour (original : C.Realization Set.univ ≃ₜ
    Metric.closedBall (0 : Plane) 1) : C.BoundaryContour (C.processedParentRetain S frontier) :=
  C.boundaryContourOfConnected _ (F.boundaryGraph_connected_of_disk _
    (Classical.choice (F.exists_processed_parent_cutDisk S roots frontier original)))

end Unfoldings.SpatialFolding
