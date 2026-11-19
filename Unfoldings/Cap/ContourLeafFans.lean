module

public import Unfoldings.Cap.LeafOpening
public import Unfoldings.Complex.ContourGapBankIndex
public import Unfoldings.Topology.ChildlessAncestors

/-! A childless positive contour source retains its entire original fan and one gap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- The contour stack at a positive leaf has exactly the gap of its own source step. -/
theorem contourSavedGapStack_leaf (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
    (starts : C.contourOriginalVertex S Q 0 ∈ P.roots) (event : C.PositiveContourSource S Q)
    (nonroot : C.positiveContourVertex S Q event ∉ P.roots)
    (childless : ∀ u ∉ P.roots, P.parent u ≠ C.positiveContourVertex S Q event) :
    C.contourSavedGapStack S Q (C.positiveContourVertex S Q event) = [event] := by
  let v := C.positiveContourVertex S Q event
  let l := C.contourSavedGapStack S Q v
  have present : event ∈ l := (C.mem_contourSavedGapStack S Q v event).mpr (P.ancestor_refl v)
  have named (g : C.PositiveContourSource S Q) (member : g ∈ l) : g = event := by
    apply C.positiveContourVertex_injective S Q roots starts
    exact (P.ancestor_childless_iff nonroot childless _).mp
      ((C.mem_contourSavedGapStack S Q v g).mp member)
  have unique : l.Nodup := C.contourSavedGapStack_nodup S Q v
  change l = [event]
  cases keys : l with
  | nil =>
    rw [keys] at present
    exact (List.not_mem_nil present).elim
  | cons g tail =>
    have at_head := named g (keys.symm ▸ List.mem_cons_self)
    subst g
    rw [keys] at unique
    have empty : tail = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro g member
      have equal := named g (keys.symm ▸ List.mem_cons_of_mem _ member)
      exact (List.nodup_cons.mp unique).1 (equal ▸ member)
    rw [empty]

/-- The source bank starts at the zero index of its own literal path. -/
theorem contourGapBankIndex_source (source : C.PositiveContourSource S Q)
    (member : source ∈ C.contourEdgeGapStack S Q (C.positiveContourVertex S Q source)) :
    C.contourGapBankIndex S Q (C.positiveContourVertex S Q source)
      (C.positiveContourVertex_nonroot S Q source) source member = 0 := by
  let v := C.positiveContourVertex S Q source
  let e := P.nonrootAncestorEquiv v
  let h := (C.mem_contourEdgeGapStack S Q v source).mp member
  let zero : Fin (P.distanceToRoot v) := ⟨0, C.positiveContourVertex_distance_pos S Q source⟩
  have at_start : e.symm ⟨v, C.positiveContourVertex_nonroot S Q source, h⟩ = zero := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext rfl
  exact (congrArg (Fin.cast (C.positiveContourBank_span S Q source)) at_start).trans (Fin.ext rfl)

end Unfoldings.TriangleComplex

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

include K in
/-- A selected leaf has one actual roof copy, whose angle includes every original corner. -/
theorem exists_selected_leaf_copy (v : C.Vertex Set.univ) (nonroot : v ∉ P.roots)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) (childless : ∀ u ∉ P.roots, P.parent u ≠ v) :
    let retain := C.selectedRetain S
    ∃ w : C.Vertex retain,
      C.vertexForgetCuts (Set.subset_univ retain) w = v ∧
      C.totalAngle retain w = C.totalAngle Set.univ v ∧
        ∀ z : C.Vertex retain, C.vertexForgetCuts (Set.subset_univ retain) z = v → z = w := by
  let retain := C.selectedRetain S
  let edge := S.edge ⟨v, nonroot⟩
  obtain ⟨p, original⟩ := exists_linkGerm_at_seam (S.link ⟨v, nonroot⟩)
  have only_cut (s : C.Seam) (removed : s ∉ retain) (w : C.Vertex Set.univ)
      (link : C.seamGraph.IsLink s v w) : s = edge :=
    S.edge_eq_at_childless nonroot childless
      (S.graph_isLink_iff.mpr ⟨not_not.mp removed, link⟩)
  have preserves := K.preserves_other_link_pairs_of_single_cut retain edge p original only_cut
  exact ⟨C.vertexOfCorner retain p.val.1, p.property,
    C.totalAngle_of_single_link_cut retain internal p preserves,
    fun z hz => C.unique_vertex_copy_of_single_link_cut retain internal p preserves z hz⟩

end Unfoldings.ConvexCap
