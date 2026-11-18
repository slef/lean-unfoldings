module

public import Unfoldings.Complex.ContourGapBankIndex
public import Unfoldings.Topology.ParentDistanceStep

/-! A terminal parent edge names the true last bank of every gap in its stack. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Actual final parent edges index the unbounded continuations at the truncation rim. -/
abbrev ContourTerminalEdge (_selection : P.EdgeSelection C.seamGraph) :=
  {v : C.Vertex Set.univ // v ∉ P.roots ∧ P.parent v ∈ P.roots}

/-- Such an edge is a genuine one-edge path to its original marked root. -/
theorem contourTerminalEdge_span (edge : C.ContourTerminalEdge S) :
    P.distanceToRoot edge.val = 1 := by
  rw [P.distanceToRoot_parent_step edge.val edge.property.1,
    (P.distanceToRoot_eq_zero_iff _).mpr edge.property.2]

theorem contourTerminalEdge_positive (edge : C.ContourTerminalEdge S) :
    0 < P.distanceToRoot edge.val := by
  rw [C.contourTerminalEdge_span S edge]
  decide

/-- No artificial terminal bank index or padded edge is used in the gap-tail attachments. -/
theorem contourGapBankIndex_last (edge : C.ContourTerminalEdge S)
    (source : C.PositiveContourSource S Q)
    (member : source ∈ C.contourEdgeGapStack S Q edge.val) :
    C.contourGapBankIndex S Q edge.val edge.property.1 source member =
      Fin.last (C.positiveContourBankLength S Q source) := by
  classical
  let k := C.contourGapBankIndex S Q edge.val edge.property.1 source member
  have at_edge := C.contourGapBankIndex_original S Q edge.val edge.property.1 source member
  have reaches : P.parent^[k.val + 1] (C.positiveContourVertex S Q source) ∈ P.roots := by
    rw [Function.iterate_succ_apply', at_edge]
    exact edge.property.2
  have minimal : P.distanceToRoot (C.positiveContourVertex S Q source) ≤ k.val + 1 :=
    Nat.find_min' (P.exists_iterate_root _) reaches
  have span := C.positiveContourBank_span S Q source
  apply Fin.ext
  have bound := k.isLt
  change k.val = C.positiveContourBankLength S Q source
  omega

/-- Every source in this stack has exactly the same actual last child vertex. -/
theorem contourGap_last_child (edge : C.ContourTerminalEdge S)
    (source : C.PositiveContourSource S Q)
    (member : source ∈ C.contourEdgeGapStack S Q edge.val) :
    P.parent^[C.positiveContourBankLength S Q source] (C.positiveContourVertex S Q source) =
      edge.val := by
  have original := C.contourGapBankIndex_original S Q edge.val edge.property.1 source member
  rw [C.contourGapBankIndex_last S Q edge source member] at original
  exact original

/-- The true terminal endpoint is the original parent of this same last child. -/
theorem contourGap_terminal_root (edge : C.ContourTerminalEdge S)
    (source : C.PositiveContourSource S Q)
    (member : source ∈ C.contourEdgeGapStack S Q edge.val) :
    P.root (C.positiveContourVertex S Q source) = P.parent edge.val := by
  have root := P.iterate_distanceToRoot_eq_root (C.positiveContourVertex S Q source)
  rw [C.positiveContourBank_span S Q source, Function.iterate_succ_apply',
    C.contourGap_last_child S Q edge source member] at root
  exact root.symm

end Unfoldings.TriangleComplex
