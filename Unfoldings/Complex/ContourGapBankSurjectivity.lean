module

public import Unfoldings.Complex.ContourGapTerminalIndex

/-! Every finite edge and the whole tail of a gap come from literal original attachments. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S)) (e : C.PositiveContourSource S Q)

/-- Every finite index is the genuine index of an original nonroot parent edge. -/
theorem exists_contourGapBankIndex_eq (i : Fin (C.positiveContourBankLength S Q e + 1)) :
    ∃ (v : C.Vertex Set.univ) (h : v ∉ P.roots) (mem : e ∈ C.contourEdgeGapStack S Q v),
      C.contourGapBankIndex S Q v h e mem = i := by
  let E := P.nonrootAncestorEquiv (C.positiveContourVertex S Q e)
  let ij := Fin.cast (C.positiveContourBank_span S Q e).symm i
  let vertex := E ij
  have mem : e ∈ C.contourEdgeGapStack S Q vertex.val :=
    (C.mem_contourEdgeGapStack S Q vertex.val e).mpr vertex.property.2
  refine ⟨vertex.val, vertex.property.1, mem, ?_⟩
  have index_eq : E.symm vertex = ij := E.symm_apply_apply ij
  change Fin.cast (C.positiveContourBank_span S Q e) (E.symm vertex) = i
  exact (congrArg (Fin.cast (C.positiveContourBank_span S Q e)) index_eq).trans
    (Fin.ext rfl)

/-- The last finite index supplies the original terminal attachment of the whole tail. -/
theorem exists_contourTerminalEdge_mem_gapStack :
    ∃ edge : C.ContourTerminalEdge S, e ∈ C.contourSavedGapStack S Q edge.val := by
  let n := C.positiveContourBankLength S Q e
  obtain ⟨v, nonroot, mem, eq⟩ := C.exists_contourGapBankIndex_eq S Q e (Fin.last n)
  have named := congrArg (fun i : Fin (n + 1) => P.parent^[i.val]
    (C.positiveContourVertex S Q e)) eq
  have original : P.parent^[n] (C.positiveContourVertex S Q e) = v :=
    named.symm.trans
      (C.contourGapBankIndex_original S Q v nonroot e mem)
  have rooted : P.parent v ∈ P.roots := by
    have finish := P.iterate_distanceToRoot_mem (C.positiveContourVertex S Q e)
    rw [C.positiveContourBank_span S Q e, Function.iterate_succ_apply', original] at finish
    exact finish
  exact ⟨⟨v, nonroot, rooted⟩,
    (C.mem_contourSavedGapStack S Q v e).mpr ((C.mem_contourEdgeGapStack S Q v e).mp mem)⟩

end Unfoldings.TriangleComplex
