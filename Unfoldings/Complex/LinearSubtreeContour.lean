module

public import Unfoldings.Complex.ContourContactFans
public import Unfoldings.Complex.SubtreeContour
public import Unfoldings.Topology.LinearTwoExits

/-! Rim-started contours completely process each descendant subtree before leaving it. -/

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
/-- Each nonroot subtree occupies one ordinary contiguous interval in the actual contour.
The order is derived from original parent banks and the original rim starting point. -/
theorem exists_linear_subtree_contour_interval (vertex : C.Vertex Set.univ)
    (nonroot : vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), enter.val < leave.val ∧
      ∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val := by
  obtain ⟨enter, leave, _distinct, enters, leaves, stable⟩ :=
    C.exists_oriented_subtree_exits S roots Q.cycle Q.closes Q.covers vertex nonroot
  have outside : ¬ C.SubtreeBoundaryInside S Q.cycle vertex 0 :=
    fun member => P.descendant_nonroot nonroot member starts
  obtain ⟨ordered, interval⟩ := finRotate_two_exits_linear_interval
    (C.SubtreeBoundaryInside S Q.cycle vertex) enter leave enters leaves stable outside
  exact ⟨enter, leave, ordered, interval⟩

include roots starts in
/-- An original descendant subtree cannot be left and then revisited in this processing order. -/
theorem contour_subtree_no_reentry (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (first middle last : Fin (Q.length + 1)) (before : first.val ≤ middle.val)
    (after : middle.val ≤ last.val)
    (first_inside : P.Ancestor (C.contourOriginalVertex S Q first) vertex)
    (last_inside : P.Ancestor (C.contourOriginalVertex S Q last) vertex) :
    P.Ancestor (C.contourOriginalVertex S Q middle) vertex := by
  obtain ⟨enter, leave, _, interval⟩ :=
    C.exists_linear_subtree_contour_interval S roots Q starts vertex nonroot
  have first_bounds := (interval first).mp first_inside
  have last_bounds := (interval last).mp last_inside
  exact (interval middle).mpr ⟨first_bounds.1.trans_le before, after.trans last_bounds.2⟩

include roots starts in
/-- All original descendants have actually been processed at the unique exit. Thus the
constructed order has the depth-first property needed by the saved-frontier construction. -/
theorem exists_completed_subtree_exit (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots) :
    ∃ enter leave : Fin (Q.length + 1), enter.val < leave.val ∧
      (∀ i, P.Ancestor (C.contourOriginalVertex S Q i) vertex ↔
        enter.val < i.val ∧ i.val ≤ leave.val) ∧
      ∀ w, P.Ancestor w vertex → w ∈ (C.contourAfterPosition S Q leave).processed := by
  obtain ⟨enter, leave, ordered, interval⟩ :=
    C.exists_linear_subtree_contour_interval S roots Q starts vertex nonroot
  refine ⟨enter, leave, ordered, interval, fun w descendant => ?_⟩
  obtain ⟨i, at_vertex⟩ := List.mem_ofFn.mp (C.mem_selectedContourSeeds S roots Q w)
  change C.contourOriginalVertex S Q i = w at at_vertex
  have bounds := (interval i).mp (at_vertex.symm ▸ descendant)
  exact at_vertex ▸ C.contour_vertex_processed_after_le S Q i leave bounds.2

end Unfoldings.TriangleComplex
