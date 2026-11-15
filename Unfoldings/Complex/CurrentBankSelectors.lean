module

public import Unfoldings.Complex.ProcessedParentCuts
public import Unfoldings.Complex.ParentBankEndpoints

/-! Recognize actual current original cut banks by their processed selector labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- The actual named side of an original parent seam is a current bank exactly when its
original child selector has been processed. No boundary-copy identification is assumed. -/
theorem selected_parent_bank_current_iff (frontier : P.ParentFrontier)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ
        (C.selectedParentCut S vertex nonroot) side) :
    C.IsBoundaryEdge (C.processedParentRetain S frontier) (C.germEdge p.val) ↔
      vertex ∈ frontier.processed := by
  have raw := congrArg (fun bank : C.BoundaryBank (C.selectedRetain S) => bank.val) named
  change C.germEdge p.val = C.seamSide (S.edge ⟨vertex, nonroot⟩) side at raw
  rw [raw]
  have boundary : C.IsBoundaryEdge (C.processedParentRetain S frontier)
      (C.seamSide (S.edge ⟨vertex, nonroot⟩) side) ↔
        S.edge ⟨vertex, nonroot⟩ ∉ C.processedParentRetain S frontier := by
    cases side
    · exact C.isBoundaryEdge_left_iff _ _
    · exact C.isBoundaryEdge_right_iff _ _
  rw [boundary, C.not_mem_processedParentRetain_iff]
  constructor
  · rintro ⟨e, processed, same⟩
    have equal := congrArg Subtype.val (S.edge_injective same)
    change e.val = vertex at equal
    exact equal ▸ processed
  · exact fun processed => ⟨⟨vertex, nonroot⟩, processed, rfl⟩

end Unfoldings.TriangleComplex
