module

public import Unfoldings.Roof.VertexExcursions
public import Unfoldings.Roof.CurvaturePrunedForest
public import Unfoldings.Complex.RestoredBankEndpoints

/-! The actual entrance and exit banks match after pruning a flat subtree. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
  (O : M.ParentBankOpening D e)

/-- Restoring the parent seam joins the two child endpoints of its named banks. -/
theorem restored_child_endpoints
    (flat : M.subtreeCurvature e.val = 0) :
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) O.enter))) =
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point O.leave)) := by
  have kept : M.selection.edge e ∈ M.curvedRetain := by
    by_contra cut
    have positive := (M.curved_parent_cut_iff e).mp cut
    rw [flat] at positive
    exact (lt_irrefl _ positive)
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex M.retain
    M.projectionContour.cycle M.projectionContour.closes O.enter)
  change C.boundaryEndVertex M.retain _ = C.boundaryEndVertex M.retain _ at next
  rw [← next]
  apply K.folding.boundary_end_forgetCuts_eq_of_restored_seam
    M.retain_subset_curvedRetain (C.selectedParentCut M.selection e.val e.property) kept
    _ _ O.side
  · simpa only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply] using O.first_named
  · exact O.last_named
  · exact (congrArg (C.vertexForgetCuts (Set.subset_univ _)) next).trans
      (O.entrance_next_vertex.trans O.exit_vertex.symm)

/-- Restoring the same seam also joins the two parent endpoints. -/
theorem restored_parent_endpoints
    (flat : M.subtreeCurvature e.val = 0) :
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) O.leave))) =
    C.vertexForgetCuts M.retain_subset_curvedRetain (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point O.enter)) := by
  have kept : M.selection.edge e ∈ M.curvedRetain := by
    by_contra cut
    have positive := (M.curved_parent_cut_iff e).mp cut
    rw [flat] at positive
    exact (lt_irrefl _ positive)
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex M.retain
    M.projectionContour.cycle M.projectionContour.closes O.leave)
  change C.boundaryEndVertex M.retain _ = C.boundaryEndVertex M.retain _ at next
  rw [← next]
  apply K.folding.boundary_end_forgetCuts_eq_of_restored_seam
    M.retain_subset_curvedRetain (C.selectedParentCut M.selection e.val e.property) kept
    _ _ (!O.side)
  · simpa only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply] using O.last_named
  · simpa only [Bool.not_not] using O.first_named
  · exact (congrArg (C.vertexForgetCuts (Set.subset_univ _)) next).trans
      (O.exit_next_vertex.trans O.entrance_vertex.symm)

end Unfoldings.ConvexRoof.SectorForest.ParentBankOpening
