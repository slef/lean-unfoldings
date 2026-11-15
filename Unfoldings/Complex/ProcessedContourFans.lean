module

public import Unfoldings.Complex.RestoredLinkChain
public import Unfoldings.Complex.ProcessedParentCuts
public import Unfoldings.Complex.SelectedContourNeighbors

/-! Already passed contour corners retain their exact final original fan at intermediate stages. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- Both original endpoints processed implies the named final bank is already a current bank. -/
theorem selected_bank_boundary_of_processed_endpoints (frontier : P.ParentFrontier)
    (p : C.BoundaryEnd (C.selectedRetain S))
    (first : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p) ∈ frontier.processed)
    (last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) p)) ∈ frontier.processed) :
    C.IsBoundaryEdge (C.processedParentRetain S frontier) (C.germEdge p.val) := by
  let bank := (C.boundaryEndEquiv (C.selectedRetain S) p).1
  rcases C.relativeBank_cases (C.selectedRetain S) Set.univ bank with old | ⟨s, side, named⟩
  · exact C.isBoundaryEdge_antitone (Set.subset_univ _) old
  · obtain ⟨e, same⟩ := (C.selectedCutSeamEquiv S).surjective s
    rw [← same] at named
    have processed : e.val ∈ frontier.processed := by
      rcases C.selected_parent_bank_endpoints S e.val e.property p side named with
        forward | backward
      · exact forward.1 ▸ first
      · exact backward.2 ▸ last
    have cut : S.edge e ∉ C.processedParentRetain S frontier :=
      (C.not_mem_processedParentRetain_iff S frontier _).mpr ⟨e, processed, rfl⟩
    have raw := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val) named
    change C.germEdge p.val = C.seamSide (S.edge e) side at raw
    rw [raw]
    cases side
    · exact (C.isBoundaryEdge_left_iff _ _).mpr cut
    · exact (C.isBoundaryEdge_right_iff _ _).mpr cut

variable (Q : C.BoundaryContour (C.selectedRetain S))

/-- Every earlier original contour label has actually been processed. -/
theorem contour_vertex_processed_of_lt (j i : Fin (Q.length + 1)) (earlier : j.val < i.val) :
    C.contourOriginalVertex S Q j ∈ (C.contourFrontier S Q i).processed := by
  apply (P.initialFrontier.mem_run_iff _ _).mpr
  refine Or.inr ⟨C.contourOriginalVertex S Q j, ?_, P.ancestor_refl _⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨j.val, ?_, ?_⟩
  · simp only [List.length_take, selectedContourSeeds, List.length_ofFn]
    omega
  · rw [List.getElem_take]
    exact C.selectedContourSeeds_getElem S Q j

/-- A previously passed original bank remains an actual bank at every later stage. -/
theorem contour_bank_boundary_of_lt (j : Fin Q.length) (i : Fin (Q.length + 1))
    (earlier : j.val + 1 < i.val) :
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point j.castSucc).val) := by
  apply C.selected_bank_boundary_of_processed_endpoints S (C.contourFrontier S Q i)
  · exact C.contour_vertex_processed_of_lt S Q j.castSucc i (by simpa using
      (show j.val < i.val from by omega))
  · have next := C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes j.castSucc
    rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt] at next
    have original := congrArg (C.relativeBoundaryVertex (Set.subset_univ _)) next
    change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.castSucc))) =
      C.contourOriginalVertex S Q j.succ at original
    rw [original]
    exact C.contour_vertex_processed_of_lt S Q j.succ i earlier

/-- After passing both adjacent banks, the actual intermediate corner contains exactly
its final original triangle corners. Later cuts elsewhere cannot change this fan. -/
theorem processed_contour_fan_corners_iff (j : Fin Q.length) (i : Fin (Q.length + 1))
    (positive : 0 < j.val) (earlier : j.val + 1 < i.val) (a : C.Corner) :
    C.vertexOfCorner (C.processedParentRetain S (C.contourFrontier S Q i)) a =
      C.vertexForgetCuts (C.selectedRetain_subset_processed S (C.contourFrontier S Q i))
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point j.castSucc)) ↔
      C.vertexOfCorner (C.selectedRetain S) a =
        C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point j.castSucc) := by
  apply C.boundary_fan_corners_iff
  · exact C.contour_bank_boundary_of_lt S Q j i earlier
  · let previous : Fin Q.length := ⟨j.val - 1, by omega⟩
    have at_next : previous.succ = j.castSucc := Fin.ext (by dsimp [previous]; omega)
    have next := Q.cycle.next previous
    change C.boundaryMate (C.selectedRetain S)
      (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc)) =
        Q.cycle.point previous.succ at next
    have mate : C.boundaryMate (C.selectedRetain S) (Q.cycle.point j.castSucc) =
        C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc) := by
      rw [← at_next, ← next, C.boundaryMate_involutive]
    rw [mate]
    have bank := C.contour_bank_boundary_of_lt S Q previous i (by dsimp [previous]; omega)
    have same := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val)
      ((C.boundaryEnd_bank_eq_iff (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc))
        (Q.cycle.point previous.castSucc)).mpr (Or.inr rfl))
    change C.germEdge _ = C.germEdge _ at same
    rw [same]
    exact bank

end Unfoldings.TriangleComplex
