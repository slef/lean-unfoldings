module

public import Unfoldings.Complex.ProcessedContourFans

/-! Identify the original fan at a contour contact immediately after the fresh child is cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- The actual processed frontier just after the named contour source. -/
def contourAfterPosition (i : Fin (Q.length + 1)) : P.ParentFrontier :=
  (C.contourFrontier S Q i).process (C.contourOriginalVertex S Q i)

/-- This includes the named source itself, and works at the final contour position. -/
theorem contour_vertex_processed_after_le (j i : Fin (Q.length + 1)) (earlier : j.val ≤ i.val) :
    C.contourOriginalVertex S Q j ∈ (C.contourAfterPosition S Q i).processed := by
  by_cases same : j = i
  · subst j
    exact ((C.contourFrontier S Q i).mem_process_iff _ _).mpr (Or.inr (P.ancestor_refl _))
  · exact Or.inl (C.contour_vertex_processed_of_lt S Q j i (by
      have distinct : j.val ≠ i.val := fun equal => same (Fin.ext equal)
      omega))

/-- The bank ending at a source is already present immediately after processing that source. -/
theorem contour_bank_boundary_after (j : Fin Q.length) (i : Fin (Q.length + 1))
    (earlier : j.val + 1 ≤ i.val) :
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourAfterPosition S Q i))
      (C.germEdge (Q.cycle.point j.castSucc).val) := by
  apply C.selected_bank_boundary_of_processed_endpoints S (C.contourAfterPosition S Q i)
  · exact C.contour_vertex_processed_after_le S Q j.castSucc i (by
      simp only [Fin.val_castSucc]
      omega)
  · have next := C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes j.castSucc
    rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt] at next
    have original := congrArg (C.relativeBoundaryVertex (Set.subset_univ _)) next
    change C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.castSucc))) =
      C.contourOriginalVertex S Q j.succ at original
    rw [original]
    exact C.contour_vertex_processed_after_le S Q j.succ i earlier

/-- At a contact, the corner immediately before the fresh incoming edge is already its
exact final original fan. This identifies actual original triangle corners, not just an angle. -/
theorem contour_contact_fan_corners_iff (i : Fin Q.length) (positive : 0 < i.val)
    (a : C.Corner) :
    C.vertexOfCorner (C.processedParentRetain S (C.contourAfterPosition S Q i.succ)) a =
      C.vertexForgetCuts (C.selectedRetain_subset_processed S (C.contourAfterPosition S Q i.succ))
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc)) ↔
      C.vertexOfCorner (C.selectedRetain S) a =
        C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc) := by
  apply C.boundary_fan_corners_iff
  · exact C.contour_bank_boundary_after S Q i i.succ le_rfl
  · let previous : Fin Q.length := ⟨i.val - 1, by omega⟩
    have at_next : previous.succ = i.castSucc := Fin.ext (by dsimp [previous]; omega)
    have next := Q.cycle.next previous
    change C.boundaryMate (C.selectedRetain S)
      (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc)) =
        Q.cycle.point previous.succ at next
    have mate : C.boundaryMate (C.selectedRetain S) (Q.cycle.point i.castSucc) =
        C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc) := by
      rw [← at_next, ← next, C.boundaryMate_involutive]
    rw [mate]
    have bank := C.contour_bank_boundary_after S Q previous i.succ (by
      dsimp [previous]
      omega)
    have same := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val)
      ((C.boundaryEnd_bank_eq_iff (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc))
        (Q.cycle.point previous.castSucc)).mpr (Or.inr rfl))
    change C.germEdge _ = C.germEdge _ at same
    rw [same]
    exact bank

/-- The contact side already has exactly its final original angle at the time it is exposed. -/
theorem contour_contact_fan_totalAngle (i : Fin Q.length) (positive : 0 < i.val) :
    C.totalAngle (C.processedParentRetain S (C.contourAfterPosition S Q i.succ))
      (C.vertexForgetCuts
        (C.selectedRetain_subset_processed S (C.contourAfterPosition S Q i.succ))
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc))) =
      C.totalAngle (C.selectedRetain S)
        (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i.castSucc)) := by
  classical
  simp only [totalAngle, C.contour_contact_fan_corners_iff S Q i positive]

end Unfoldings.TriangleComplex
