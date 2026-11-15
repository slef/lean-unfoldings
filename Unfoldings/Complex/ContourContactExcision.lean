module

public import Unfoldings.Complex.ContourContactFans
public import Unfoldings.Complex.BoundaryFanExcision

/-! The actual original contour supplies whole-ball metric restoration at its contact corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Both terminal banks of the original contact fan are already present in the current cut. -/
theorem contour_contact_terminal_banks (i : Fin Q.length) (positive : 0 < i.val) :
    let current := C.processedParentRetain S (C.contourAfterPosition S Q i.succ)
    let p := Q.cycle.point i.castSucc
    C.IsBoundaryEdge current (C.germEdge p.val) ∧
      C.IsBoundaryEdge current
        (C.germEdge (C.boundaryMate (C.selectedRetain S) p).val) := by
  dsimp only
  refine ⟨C.contour_bank_boundary_after S Q i i.succ le_rfl, ?_⟩
  let previous : Fin Q.length := ⟨i.val - 1, by omega⟩
  have at_next : previous.succ = i.castSucc := Fin.ext (by dsimp [previous]; omega)
  have next := Q.cycle.next previous
  change C.boundaryMate (C.selectedRetain S)
    (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc)) =
      Q.cycle.point previous.succ at next
  have mate : C.boundaryMate (C.selectedRetain S) (Q.cycle.point i.castSucc) =
      C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc) := by
    rw [← at_next, ← next, C.boundaryMate_involutive]
  rw [mate]
  have bank := C.contour_bank_boundary_after S Q previous i.succ (by dsimp [previous]; omega)
  have same := congrArg (fun b : C.BoundaryBank (C.selectedRetain S) => b.val)
    ((C.boundaryEnd_bank_eq_iff (C.selectedRetain S)
      (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point previous.castSucc))
      (Q.cycle.point previous.castSucc)).mpr (Or.inr rfl))
  change C.germEdge _ = C.germEdge _ at same
  rw [same]
  exact bank

/-- The canonical map from the final original cut to the actual intermediate cut preserves
one whole intrinsic ball at this contact. The radius and the isometry are constructed. -/
theorem exists_contour_contact_forgetChart (i : Fin Q.length) (positive : 0 < i.val) :
    Nonempty (MetricGluing.ForgetChart C.Cell
      (C.glue_mono (C.selectedRetain_subset_processed S (C.contourAfterPosition S Q i.succ)))
      (C.cornerPoint (Q.cycle.point i.castSucc).val.1)) := by
  obtain ⟨first, last⟩ := C.contour_contact_terminal_banks S Q i positive
  exact C.exists_boundary_fan_forgetChart
    (C.selectedRetain_subset_processed S (C.contourAfterPosition S Q i.succ))
    (Q.cycle.point i.castSucc) first last

end Unfoldings.TriangleComplex
