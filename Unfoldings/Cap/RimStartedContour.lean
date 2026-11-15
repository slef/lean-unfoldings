module

public import Unfoldings.Cap.Topology
public import Unfoldings.Complex.RimStartedContour

/-! Construct original cap cut contours whose first vertex lies on the original rim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)

include K roots in
/-- The original cap disk supplies a rim vertex and the actual cut disk supplies its cyclic order.
Neither a starting root nor a separate contour certificate is required from the caller. -/
theorem exists_rim_started_selected_contour :
    ∃ Q : C.BoundaryContour (C.selectedRetain S),
      C.contourOriginalVertex S Q 0 ∈ P.roots := by
  obtain ⟨root⟩ := (K.folding.boundaryGraph_connected_of_disk Set.univ K.diskHomeomorph).nonempty
  have marked : root.val ∈ P.roots := roots.symm ▸ root.property
  let Q := C.boundaryContourOfConnected (C.selectedRetain S)
    (K.folding.boundaryGraph_connected_of_disk _
      (C.selectedCutDisk S roots K.folding K.diskHomeomorph))
  obtain ⟨R, first⟩ := C.exists_rim_started_contour S roots Q root.val marked
  exact ⟨R, first.symm ▸ marked⟩

/-- The actual cap contour used for singleton fresh-branch scheduling. -/
def rimStartedSelectedContour : C.BoundaryContour (C.selectedRetain S) :=
  (K.exists_rim_started_selected_contour S roots).choose

theorem rimStartedSelectedContour_starts :
    C.contourOriginalVertex S (K.rimStartedSelectedContour S roots) 0 ∈ P.roots :=
  (K.exists_rim_started_selected_contour S roots).choose_spec

/-- No initial long branch or hidden original-ancestor charge occurs for this constructed order. -/
theorem rimStartedSelectedContour_contactTime_le_one
    (i : Fin ((K.rimStartedSelectedContour S roots).length + 1)) :
    (C.contourFrontier S (K.rimStartedSelectedContour S roots) i).contactTime
      (C.contourOriginalVertex S (K.rimStartedSelectedContour S roots) i) ≤ 1 :=
  C.rim_contour_contactTime_le_one S roots (K.rimStartedSelectedContour S roots)
    (K.rimStartedSelectedContour_starts S roots) i

end Unfoldings.ConvexCap
