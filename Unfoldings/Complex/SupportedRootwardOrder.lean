module

public import Unfoldings.Complex.SupportedRootwardBanks
public import Unfoldings.Complex.RootwardBoundaryStep
public import Unfoldings.Complex.ContourActiveAncestors

/-! Actual ancestor order and completed side subtrees allow unused isolated roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (boundary_roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include boundary_roots starts in
/-- Strict original ancestry forces the strict order of the actual surviving bank indices. -/
theorem rootward_bank_index_lt_of_ancestor_of_boundary_roots (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (ancestor : P.Ancestor (C.contourOriginalVertex S Q j.val)
      (C.contourOriginalVertex S Q k.val))
    (different : C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val) :
    j.val.val < k.val.val := by
  have data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  obtain ⟨enter, leave, side, _ordered, interval, first, last⟩ :=
    C.exists_named_linear_subtree_interval_of_boundary_roots S boundary_roots Q starts
      (C.contourOriginalVertex S Q k.val) data.1
  obtain ⟨_, other, named⟩ := C.future_current_bank_named_of_boundary_roots S boundary_roots Q
    starts i k.val
    k.property.1 k.property.2.1 k.property.2.2
  have at_leave : k.val = leave := by
    rcases C.named_parent_bank_index_eq S Q (C.contourOriginalVertex S Q k.val) data.1
        enter leave k.val side other first last named with at_entry | at_leave
    · have bounds := (interval i).mp data.2.2.1
      have future := k.property.1
      have values := congrArg Fin.val at_entry
      omega
    · exact at_leave
  have bounds := (interval j.val).mp ancestor
  have le_index : j.val.val ≤ k.val.val := by simpa only [at_leave] using bounds.2
  have ne_index : j.val.val ≠ k.val.val := by
    intro same
    exact different (congrArg (C.contourOriginalVertex S Q) (Fin.ext same))
  omega

include boundary_roots starts in
/-- The bank order strictly increases the original potential. The stored edges are therefore
in their original rootward order and cannot repeat or reverse an original ancestor segment. -/
theorem rootward_bank_order_of_parent_of_boundary_roots (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) : j.val.val < k.val.val := by
  have data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val
    j.property.1 j.property.2.1 j.property.2.2
  apply C.rootward_bank_index_lt_of_ancestor_of_boundary_roots S boundary_roots Q starts i j k
  · exact parent ▸ P.ancestor_parent (C.contourOriginalVertex S Q j.val)
  · intro same
    have fixed := parent.trans same.symm
    exact (P.ascending _ data.1).ne (congrArg P.height fixed).symm

include boundary_roots starts in
/-- The ordinary bank-index order is exactly the strict original ancestor order. -/
theorem rootward_bank_index_lt_iff_of_boundary_roots (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i) :
    j.val.val < k.val.val ↔
      P.Ancestor (C.contourOriginalVertex S Q j.val) (C.contourOriginalVertex S Q k.val) ∧
        C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val := by
  constructor
  · intro before
    have different : C.contourOriginalVertex S Q j.val ≠ C.contourOriginalVertex S Q k.val := by
      intro same
      have bank_eq : j = k := (C.rootwardBankEquiv_of_boundary_roots S boundary_roots Q starts
        i).injective
        (Subtype.ext same)
      exact before.ne (congrArg (fun b : C.RootwardBank S Q i => b.val.val) bank_eq)
    have first := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i j.val
      j.property.1 j.property.2.1 j.property.2.2
    have last := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i k.val
      k.property.1 k.property.2.1 k.property.2.2
    rcases P.ancestors_comparable first.2.2.1 last.2.2.1 with forward | backward
    · exact ⟨forward, different⟩
    · have reverse := C.rootward_bank_index_lt_of_ancestor_of_boundary_roots S boundary_roots Q
        starts i k j backward different.symm
      omega
  · exact fun both => C.rootward_bank_index_lt_of_ancestor_of_boundary_roots S boundary_roots Q
      starts i j k both.1 both.2


include boundary_roots starts in
/-- A processed nonroot outside the current ancestor path has no remaining fresh descendants.
This is an actual property of the constructed prefix state, not an assumed stack invariant. -/
theorem processed_nonancestor_subtree_complete_of_boundary_roots (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (off_path : ¬ P.Ancestor (C.contourOriginalVertex S Q i) vertex) :
    ∀ w, P.Ancestor w vertex → w ∈ (C.contourFrontier S Q i).processed := by
  intro w descendant
  by_contra fresh
  obtain root | ⟨first, before, at_vertex⟩ :=
    (C.rim_contour_processed_iff_of_boundary_roots S boundary_roots Q starts i vertex).mp processed
  · exact nonroot root
  · obtain ⟨last, at_w⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds_of_nonroot S Q w
      (P.descendant_nonroot nonroot descendant))
    change C.contourOriginalVertex S Q last = w at at_w
    have after : i.val ≤ last.val := by
      by_contra earlier
      exact fresh (at_w ▸ C.contour_vertex_processed_of_lt S Q last i (by omega))
    apply off_path
    exact C.contour_subtree_no_reentry_of_boundary_roots S boundary_roots Q starts vertex nonroot
      first i last before.le after
      (at_vertex.symm ▸ P.ancestor_refl vertex) (at_w.symm ▸ descendant)

include boundary_roots starts in
/-- Every already processed nonroot with a still fresh descendant belongs to the current
original parent path. No unfinished side branch can serve as a competing saved stem. -/
theorem unfinished_processed_vertex_is_ancestor_of_boundary_roots (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (unfinished : ∃ w, P.Ancestor w vertex ∧ w ∉ (C.contourFrontier S Q i).processed) :
    P.Ancestor (C.contourOriginalVertex S Q i) vertex := by
  by_contra off_path
  obtain ⟨w, descendant, fresh⟩ := unfinished
  exact fresh (C.processed_nonancestor_subtree_complete_of_boundary_roots S boundary_roots Q
    starts i vertex nonroot
    processed off_path w descendant)

include boundary_roots starts in
/-- A previously processed child of the current contour vertex has its whole descendant
subtree completed. Only unprocessed children remain on the future side of the contour. -/
theorem processed_contour_child_subtree_complete_of_boundary_roots (i : Fin (Q.length + 1))
    (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    (parent : P.parent child = C.contourOriginalVertex S Q i)
    (processed : child ∈ (C.contourFrontier S Q i).processed) :
    ∀ w, P.Ancestor w child → w ∈ (C.contourFrontier S Q i).processed := by
  apply C.processed_nonancestor_subtree_complete_of_boundary_roots S boundary_roots Q starts i
    child nonroot processed
  rw [← parent]
  exact P.not_ancestor_parent_self nonroot


include boundary_roots starts in
/-- All intervening original contour banks are restored. Their entire fresh subtrees can
therefore be skipped when constructing the actual current rootward boundary chain. -/
theorem consecutive_rootward_banks_restored_of_boundary_roots (i : Fin (Q.length + 1))
    (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val)
    (l : Fin (Q.length + 1)) (after : j.val.val < l.val) (before : l.val < k.val.val) :
    ¬ C.IsBoundaryEdge (C.processedParentRetain S (C.contourFrontier S Q i))
      (C.germEdge (Q.cycle.point l).val) := by
  intro current
  have future : i.val ≤ l.val := j.property.1.trans after.le
  have last_data := C.future_current_bank_rootward_of_boundary_roots S boundary_roots Q starts i
    k.val
    k.property.1 k.property.2.1 k.property.2.2
  by_cases rim : C.IsBoundaryEdge Set.univ (C.germEdge (Q.cycle.point l).val)
  · let original_end : C.BoundaryEnd Set.univ := ⟨(Q.cycle.point l).val, rim⟩
    have root : C.contourOriginalVertex S Q l ∈ P.roots :=
      boundary_roots <| (C.boundaryEndAsVertex Set.univ original_end).property
    have inside := C.contour_subtree_no_reentry_of_boundary_roots S boundary_roots Q starts
      (C.contourOriginalVertex S Q k.val) last_data.1 j.val l k.val after.le before.le
      (parent ▸ P.ancestor_parent _) (P.ancestor_refl _)
    exact P.descendant_nonroot last_data.1 inside root
  · let middle : C.RootwardBank S Q i := ⟨l, future, current, rim⟩
    have first := (C.rootward_bank_index_lt_iff_of_boundary_roots S boundary_roots Q starts i j
      middle).mp after
    have last := (C.rootward_bank_index_lt_iff_of_boundary_roots S boundary_roots Q starts i
      middle k).mp before
    have step : P.Ancestor (C.contourOriginalVertex S Q middle.val)
        (P.parent (C.contourOriginalVertex S Q j.val)) := parent.symm ▸ last.1
    rcases P.ancestor_between_parent first.1 step with at_child | at_parent
    · exact first.2 at_child.symm
    · exact last.2 (at_parent.trans parent)


end Unfoldings.TriangleComplex
