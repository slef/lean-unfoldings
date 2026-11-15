module

public import Unfoldings.Complex.LinearSubtreeContour
public import Unfoldings.Complex.RimStartedContour

/-! Unfinished processed contour vertices lie on the current original ancestor path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)

include roots starts in
/-- A processed nonroot outside the current ancestor path has no remaining fresh descendants.
This is an actual property of the constructed prefix state, not an assumed stack invariant. -/
theorem processed_nonancestor_subtree_complete (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (off_path : ¬ P.Ancestor (C.contourOriginalVertex S Q i) vertex) :
    ∀ w, P.Ancestor w vertex → w ∈ (C.contourFrontier S Q i).processed := by
  intro w descendant
  by_contra fresh
  obtain root | ⟨first, before, at_vertex⟩ :=
    (C.rim_contour_processed_iff S roots Q starts i vertex).mp processed
  · exact nonroot root
  · obtain ⟨last, at_w⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds S roots Q w)
    change C.contourOriginalVertex S Q last = w at at_w
    have after : i.val ≤ last.val := by
      by_contra earlier
      exact fresh (at_w ▸ C.contour_vertex_processed_of_lt S Q last i (by omega))
    apply off_path
    exact C.contour_subtree_no_reentry S roots Q starts vertex nonroot first i last before.le after
      (at_vertex.symm ▸ P.ancestor_refl vertex) (at_w.symm ▸ descendant)

include roots starts in
/-- Every already processed nonroot with a still fresh descendant belongs to the current
original parent path. No unfinished side branch can serve as a competing saved stem. -/
theorem unfinished_processed_vertex_is_ancestor (i : Fin (Q.length + 1))
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (processed : vertex ∈ (C.contourFrontier S Q i).processed)
    (unfinished : ∃ w, P.Ancestor w vertex ∧ w ∉ (C.contourFrontier S Q i).processed) :
    P.Ancestor (C.contourOriginalVertex S Q i) vertex := by
  by_contra off_path
  obtain ⟨w, descendant, fresh⟩ := unfinished
  exact fresh (C.processed_nonancestor_subtree_complete S roots Q starts i vertex nonroot
    processed off_path w descendant)

include roots starts in
/-- A previously processed child of the current contour vertex has its whole descendant
subtree completed. Only unprocessed children remain on the future side of the contour. -/
theorem processed_contour_child_subtree_complete (i : Fin (Q.length + 1))
    (child : C.Vertex Set.univ) (nonroot : child ∉ P.roots)
    (parent : P.parent child = C.contourOriginalVertex S Q i)
    (processed : child ∈ (C.contourFrontier S Q i).processed) :
    ∀ w, P.Ancestor w child → w ∈ (C.contourFrontier S Q i).processed := by
  apply C.processed_nonancestor_subtree_complete S roots Q starts i child nonroot processed
  rw [← parent]
  exact P.not_ancestor_parent_self nonroot

end Unfoldings.TriangleComplex
