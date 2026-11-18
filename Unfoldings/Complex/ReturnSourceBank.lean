module

public import Unfoldings.Complex.SupportedProcessedRootwardChain
public import Unfoldings.Complex.ProcessedContourFans

/-! The source edge on a contour return survives in the actual new cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S)) (j : Fin Q.length)

/-- The true far endpoint of the outgoing contour bank has the next original contour label. -/
theorem contourBank_finish_original :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S)
        (C.boundaryTurn (C.selectedRetain S) (Q.cycle.point j.castSucc))) =
      C.contourOriginalVertex S Q j.succ := by
  have next := congrArg Subtype.val
    (C.boundaryCycle_next_vertex (C.selectedRetain S) Q.cycle Q.closes j.castSucc)
  rw [show finRotate (Q.length + 1) j.castSucc = j.succ from finRotate_of_lt j.isLt] at next
  exact congrArg (C.vertexForgetCuts (Set.subset_univ _)) next

/-- Both ends of the returning source edge are processed after the source's actual step. -/
theorem returnSourceBank_survives
    (returns : P.parent (C.contourOriginalVertex S Q j.castSucc) =
      C.contourOriginalVertex S Q j.succ) :
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q j.succ))
      (C.germEdge (Q.cycle.point j.castSucc).val) := by
  have processed := C.previous_contour_vertex_processed S Q j
  apply C.selected_bank_boundary_of_processed_endpoints S (C.contourFrontier S Q j.succ)
    (Q.cycle.point j.castSucc) processed
  rw [C.contourBank_finish_original S Q j, ← returns]
  exact (C.contourFrontier S Q j.succ).closed _ processed

/-- Keep the literal returning bank, with its original tagged endpoint and direction. -/
def returnSourceBank
    (returns : P.parent (C.contourOriginalVertex S Q j.castSucc) =
      C.contourOriginalVertex S Q j.succ) :
    C.BoundaryEnd (C.processedParentRetain S (C.contourFrontier S Q j.succ)) :=
  C.survivingBoundaryEnd (Q.cycle.point j.castSucc) (C.returnSourceBank_survives S Q j returns)

/-- A fresh source step is either a descent to its child or a return to its parent. -/
theorem fresh_contour_step_direction (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
    (fresh : C.contourOriginalVertex S Q j.castSucc ∉
      (C.contourFrontier S Q j.castSucc).processed) :
    P.parent (C.contourOriginalVertex S Q j.succ) = C.contourOriginalVertex S Q j.castSucc ∨
      P.parent (C.contourOriginalVertex S Q j.castSucc) = C.contourOriginalVertex S Q j.succ := by
  rcases C.contourOriginalVertex_neighbors_of_boundary_roots S roots Q j with
    descent | returns | boundary
  · exact Or.inl descent
  · exact Or.inr returns
  · exact (fresh ((C.contourFrontier S Q j.castSucc).roots boundary.1)).elim

end Unfoldings.TriangleComplex
