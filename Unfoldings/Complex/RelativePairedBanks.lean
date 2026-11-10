module

public import Unfoldings.Complex.RelativeCutGraph
public import Unfoldings.Complex.PairedBankComponents

/-!
# Opposite banks of relative forest cuts share a boundary component

Original banks map to two outside spokes. New banks map to their named cut
edge. If the outside extension is acyclic, the alternate boundary path through
one bank must contain the other bank of that same seam.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

private theorem relativeBoundaryLink_reaches_avoiding_cut
    (s : C.RelativeCutSeam small large) (bank : C.BoundaryBank small)
    (not_first : bank ≠ C.relativeCutBank small large s false)
    (not_last : bank ≠ C.relativeCutBank small large s true)
    {u v : C.BoundaryVertex small} (link : (C.boundaryGraph small).graph.IsLink bank u v) :
    ((C.relativeCutRootExtension small large).deleteEdges {Sum.inl s}).Reaches
      (some (C.relativeBoundaryVertex inclusion u))
      (some (C.relativeBoundaryVertex inclusion v)) := by
  let H := C.relativeCutRootExtension small large
  have canonical : (H.deleteEdges {Sum.inl s}).Reaches
      (some (C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).left bank)))
      (some (C.relativeBoundaryVertex inclusion ((C.boundaryGraph small).right bank))) := by
    rcases C.relativeBank_cases small large bank with old | ⟨t, side, rfl⟩
    · let leftRoot : C.relativeCutRoots large :=
        ⟨_, C.relativeBoundaryVertex_old_left inclusion bank old⟩
      let rightRoot : C.relativeCutRoots large :=
        ⟨_, C.relativeBoundaryVertex_old_right inclusion bank old⟩
      have first : (H.deleteEdges {Sum.inl s}).IsLink (Sum.inr leftRoot)
          (some leftRoot.val) none :=
        ⟨((C.relativeCutGraph small large).rootExtension_spoke _ leftRoot).symm, by simp⟩
      have last : (H.deleteEdges {Sum.inl s}).IsLink (Sum.inr rightRoot)
          none (some rightRoot.val) :=
        ⟨(C.relativeCutGraph small large).rootExtension_spoke _ rightRoot, by simp⟩
      exact (Graph.Reaches.of_isLink first).trans (Graph.Reaches.of_isLink last)
    · have different : t ≠ s := by
        rintro rfl
        cases side
        · exact not_first rfl
        · exact not_last rfl
      exact Graph.Reaches.of_isLink
        ⟨(C.relativeCutGraph_bank_link inclusion t side).rootExtension _, by
          simpa only [Set.mem_singleton_iff, Sum.inl.injEq] using different⟩
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact canonical
  · exact canonical.symm

include inclusion in
theorem relativeOppositeBanks_reaches
    (forest : (C.relativeCutRootExtension small large).IsAcyclic)
    (s : C.RelativeCutSeam small large) (side : Bool) :
    (C.boundaryGraph small).graph.Reaches
      ((C.boundaryGraph small).left (C.relativeCutBank small large s side))
      ((C.boundaryGraph small).left (C.relativeCutBank small large s (!side))) := by
  let G := C.boundaryGraph small
  let H := C.relativeCutRootExtension small large
  let bank := C.relativeCutBank small large s side
  let other := C.relativeCutBank small large s (!side)
  obtain ⟨u, v, detour, cycle⟩ := C.boundaryGraph_bank_liesOnCycle small bank
  have member : other ∈ detour := by
    by_contra absent
    have alt : (H.deleteEdges {Sum.inl s}).Reaches
        (some (C.relativeBoundaryVertex inclusion u))
        (some (C.relativeBoundaryVertex inclusion v)) := by
      apply cycle.isPath.isWalk.mapReachability (H := H.deleteEdges {Sum.inl s})
        (fun p => some (C.relativeBoundaryVertex inclusion p))
        (fun p _ => Or.inl (C.relativeBoundaryVertex_member inclusion p))
      intro f member a b link
      apply C.relativeBoundaryLink_reaches_avoiding_cut inclusion s f _ _ link
      all_goals
        intro equal
        rw [equal] at member
        cases side
        all_goals first | exact cycle.notMem member | exact absent member
    have actual : H.IsLink (Sum.inl s) (some (C.relativeBoundaryVertex inclusion u))
        (some (C.relativeBoundaryVertex inclusion v)) := by
      have own := (C.relativeCutGraph_bank_link inclusion s side).rootExtension
        (C.relativeCutRoots large)
      rcases cycle.isLink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact own
      · exact own.symm
    exact (forest.isBridge actual.edge_mem).not_reaches actual alt
  have own_link : G.graph.IsLink bank (G.left bank) (G.right bank) := Or.inl ⟨rfl, rfl⟩
  have other_link : G.graph.IsLink other (G.left other) (G.right other) := Or.inl ⟨rfl, rfl⟩
  have source : G.graph.Reaches (G.left bank) u := by
    rcases cycle.isLink.left_eq_or_eq own_link with rfl | rfl
    · exact Graph.Reaches.refl own_link.left_mem
    · exact Graph.Reaches.of_isLink own_link
  exact source.trans (cycle.isPath.isWalk.reaches_mem_walkVertices
    (Graph.mem_walkVertices_of_mem_covered ⟨_, member, other_link.inc_left⟩))

include inclusion in
theorem relativeBoundaryEnds_reaches
    (forest : (C.relativeCutRootExtension small large).IsAcyclic)
    (s : C.RelativeCutSeam small large) (side : Bool) (b c : Bool) :
    (C.boundaryGraph small).graph.Reaches
      (C.boundaryEndAsVertex small ((C.boundaryEndEquiv small).symm
        (C.relativeCutBank small large s side, b)))
      (C.boundaryEndAsVertex small ((C.boundaryEndEquiv small).symm
        (C.relativeCutBank small large s (!side), c))) := by
  have first := C.boundaryEnd_reaches_bank_left small
    ((C.boundaryEndEquiv small).symm (C.relativeCutBank small large s side, b))
  have last := C.boundaryEnd_reaches_bank_left small
    ((C.boundaryEndEquiv small).symm (C.relativeCutBank small large s (!side), c))
  simp only [Equiv.apply_symm_apply] at first last
  exact first.trans ((C.relativeOppositeBanks_reaches inclusion forest s side).trans last.symm)

end Unfoldings.TriangleComplex
