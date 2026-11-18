module

public import Unfoldings.Complex.ContourGapStacks
public import Unfoldings.Topology.ParentOrbitEnumeration

/-! Each original parent-edge occurrence in a canonical gap stack has its exact gap-bank index. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- A fresh positive source is never a marked root. -/
theorem positiveContourVertex_nonroot (source : C.PositiveContourSource S Q) :
    C.positiveContourVertex S Q source ∉ P.roots := by
  intro rooted
  exact source.property.1 ((C.contourFrontier S Q source.val.castSucc).roots rooted)

theorem positiveContourVertex_distance_pos (source : C.PositiveContourSource S Q) :
    0 < P.distanceToRoot (C.positiveContourVertex S Q source) := by
  have nonroot := C.positiveContourVertex_nonroot S Q source
  exact Nat.pos_of_ne_zero (fun zero => nonroot ((P.distanceToRoot_eq_zero_iff _).mp zero))

/-- The chain index includes every actual parent edge and requires no padded zero-length bank. -/
def positiveContourBankLength (source : C.PositiveContourSource S Q) : ℕ :=
  P.distanceToRoot (C.positiveContourVertex S Q source) - 1

theorem positiveContourBank_span (source : C.PositiveContourSource S Q) :
    P.distanceToRoot (C.positiveContourVertex S Q source) =
      C.positiveContourBankLength S Q source + 1 := by
  have positive := C.positiveContourVertex_distance_pos S Q source
  dsimp only [positiveContourBankLength]
  omega

/-- An original parent bank has its unique actual index in each gap touching that bank. -/
def contourGapBankIndex (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (source : C.PositiveContourSource S Q) (member : source ∈ C.contourEdgeGapStack S Q vertex) :
    Fin (C.positiveContourBankLength S Q source + 1) :=
  Fin.cast (C.positiveContourBank_span S Q source)
    ((P.nonrootAncestorEquiv (C.positiveContourVertex S Q source)).symm
      ⟨vertex, nonroot, (C.mem_contourEdgeGapStack S Q vertex source).mp member⟩)

/-- The bank index retains the original vertex label exactly, before any planar placement. -/
theorem contourGapBankIndex_original (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (source : C.PositiveContourSource S Q) (member : source ∈ C.contourEdgeGapStack S Q vertex) :
    P.parent^[(C.contourGapBankIndex S Q vertex nonroot source member).val]
      (C.positiveContourVertex S Q source) = vertex :=
  congrArg Subtype.val
    ((P.nonrootAncestorEquiv (C.positiveContourVertex S Q source)).apply_symm_apply
    ⟨vertex, nonroot, (C.mem_contourEdgeGapStack S Q vertex source).mp member⟩)

end Unfoldings.TriangleComplex
