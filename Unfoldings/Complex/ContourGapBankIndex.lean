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

/-- Following one original parent edge advances the same gap's finite bank index by one. -/
theorem contourGapBankIndex_parent (v : C.Vertex Set.univ) (nonroot : v ∉ P.roots)
    (parent_nonroot : P.parent v ∉ P.roots)
    (source : C.PositiveContourSource S Q)
    (here : source ∈ C.contourEdgeGapStack S Q v)
    (above : source ∈ C.contourEdgeGapStack S Q (P.parent v)) :
    (C.contourGapBankIndex S Q (P.parent v) parent_nonroot source above).val =
      (C.contourGapBankIndex S Q v nonroot source here).val + 1 := by
  let rootSource := C.positiveContourVertex S Q source
  let i := C.contourGapBankIndex S Q v nonroot source here
  let j := C.contourGapBankIndex S Q (P.parent v) parent_nonroot source above
  have next : P.parent^[i.val + 1] rootSource = P.parent v := by
    rw [Function.iterate_succ_apply', C.contourGapBankIndex_original]
  have before : i.val + 1 < P.distanceToRoot rootSource := by
    by_contra! at_root
    have reached : P.parent^[i.val + 1] rootSource ∈ P.roots := by
      rw [← Nat.sub_add_cancel at_root, Function.iterate_add_apply,
        Function.iterate_fixed (P.fixed_root _ (P.iterate_distanceToRoot_mem rootSource))]
      exact P.iterate_distanceToRoot_mem rootSource
    exact parent_nonroot (next ▸ reached)
  have dj : j.val < P.distanceToRoot rootSource :=
    (C.positiveContourBank_span S Q source).symm ▸ j.isLt
  let E := P.nonrootAncestorEquiv rootSource
  have eq : E ⟨j.val, dj⟩ = E ⟨i.val + 1, before⟩ := by
    apply Subtype.ext
    exact (C.contourGapBankIndex_original S Q (P.parent v) parent_nonroot source above).trans
      next.symm
  exact congrArg Fin.val (E.injective eq)

end Unfoldings.TriangleComplex
