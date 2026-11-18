module

public import Unfoldings.Complex.ProcessedContourPrefix
public import Unfoldings.Roof.SurvivingBankAccuracy

/-! Actual passed original contour sides retain their current physical and metric rolling data. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S)) (stage : Fin (Q.length + 1))
  (length : ℕ) (past : length + 1 < stage.val)

theorem processedContourPrefix_phase_error (j : Fin (length + 1)) :
    K.projectedMetricHeadingError (C.processedContourPrefix S Q stage length past) j =
      K.projectedMetricHeadingError
        (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega)) j :=
  K.survivingBoundaryChain_phase_error
    (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) _ _ j

theorem processedContourPrefix_projected :
    K.folding.projectedBoundaryChain (C.processedContourPrefix S Q stage length past) =
      K.folding.projectedBoundaryChain
        (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega)) :=
  K.folding.survivingBoundaryChain_projected
    (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) _ _

/-- Bounds follow the same untouched side with all actual bank labels derived from the history. -/
theorem processedContourPrefix_accuracy {error lengthConstant : ℝ}
    (data : K.BankRollAccuracy error lengthConstant (C.selectedRetain S)
      (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega))) :
    K.BankRollAccuracy error lengthConstant
      (C.processedParentRetain S (C.contourFrontier S Q stage))
      (C.processedContourPrefix S Q stage length past) :=
  K.survivingBoundaryChain_accuracy
    (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) _ _ data

end Unfoldings.ConvexRoof
