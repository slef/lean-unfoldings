module

public import Unfoldings.Complex.ProcessedContourFans
public import Unfoldings.Complex.SurvivingBoundaryTrace
public import Unfoldings.Topology.ChainInterval

/-! Already passed original contour banks form an exact untouched chain at every later cut stage. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Every bank of the passed prefix remains an actual current cut bank. -/
theorem processedContourPrefix_survives (stage : Fin (Q.length + 1))
    (length : ℕ) (past : length + 1 < stage.val) (j : Fin (length + 1)) :
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q stage))
      (C.germEdge ((Q.cycle.interval 0 length (by have _bound := stage.isLt; omega)).point
        j).val) := by
  have _bound := stage.isLt
  have vertex_bound := j.isLt
  have named : (Q.cycle.interval 0 length (by omega)).point j =
      Q.cycle.point ⟨j.val, by omega⟩ := congrArg Q.cycle.point (Fin.ext (Nat.zero_add j.val))
  have bank := C.contour_bank_boundary_of_lt S Q (⟨j.val, by omega⟩ : Fin Q.length) stage
    (by change j.val + 1 < stage.val; omega)
  exact Eq.mpr (congrArg (fun p : C.BoundaryEnd (C.selectedRetain S) =>
    C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q stage))
      (C.germEdge p.val)) named) bank

/-- Construct the untouched passed prefix on the actual intermediate cut surface. -/
def processedContourPrefix (stage : Fin (Q.length + 1)) (length : ℕ)
    (past : length + 1 < stage.val) :
    (C.boundarySystem (C.processedParentRetain S (C.contourFrontier S Q stage))).Chain length :=
  C.survivingBoundaryChain (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage))
    (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega))
    (C.processedContourPrefix_survives S Q stage length past)

/-- Every normalized intrinsic point and all unreduced turns of the untouched side are fixed. -/
theorem processedContourPrefix_roll (stage : Fin (Q.length + 1)) (length : ℕ)
    (past : length + 1 < stage.val) :
    C.boundaryChainRoll (C.processedContourPrefix S Q stage length past) =
      C.boundaryChainRoll (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega)) :=
  C.survivingBoundaryChain_roll
    (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) _ _

/-- The whole original closed metric trace survives in the same intermediate cut copies. -/
theorem processedContourPrefix_trace (stage : Fin (Q.length + 1)) (length : ℕ)
    (past : length + 1 < stage.val) :
    C.boundaryChainTrace (C.processedContourPrefix S Q stage length past) =
      C.forgetCuts (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) ''
        C.boundaryChainTrace (Q.cycle.interval 0 length (by have _bound := stage.isLt; omega)) :=
  C.survivingBoundaryChain_trace
    (C.selectedRetain_subset_processed S (C.contourFrontier S Q stage)) _ _

end Unfoldings.TriangleComplex
