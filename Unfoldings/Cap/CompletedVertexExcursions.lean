module

public import Unfoldings.Cap.CompletedContourExcursion
public import Unfoldings.Topology.CyclicSubintervals

/-! Construct actual contour prefixes and suffixes between developed copies of a branch vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots}}
  (O : N.ParentBankOpening D e)

theorem entrance_next_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) O.enter))) =
        e.val := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex N.completedRetain
    N.completedContour.cycle N.completedContour.closes O.enter)
  change C.boundaryEndVertex N.completedRetain
    (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.enter)) =
      C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) O.enter)) at next
  rw [← next]
  exact (C.selected_parent_bank_enters N.spanningCompletion.selection e.val e.property
    (N.completedContour.cycle.point O.enter) O.side O.first_named O.outside).2

theorem exit_next_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex N.completedRetain
      (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) O.leave))) =
        N.spanningCompletion.parents.parent e.val := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex N.completedRetain
    N.completedContour.cycle N.completedContour.closes O.leave)
  change C.boundaryEndVertex N.completedRetain
    (C.boundaryTurn N.completedRetain (N.completedContour.cycle.point O.leave)) =
      C.boundaryEndVertex N.completedRetain
        (N.completedContour.cycle.point (finRotate (N.completedContour.length + 1) O.leave)) at next
  rw [← next]
  exact (C.selected_parent_bank_leaves N.spanningCompletion.selection e.val e.property
    (N.completedContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2

/-- Every other copy of the child vertex is reached by a genuine contour prefix inside its
descendant region. The prefix starts immediately after the parent's entrance bank. -/
theorem exists_entrance_excursion (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val)
    (different : finRotate (N.completedContour.length + 1) O.enter ≠ target) :
    ∃ E : N.ContourExcursion e,
      finRotate (N.completedContour.length + 1) E.first =
        finRotate (N.completedContour.length + 1) O.enter ∧
      finRotate (N.completedContour.length + 1) E.last = target := by
  have target_inside : C.SubtreeBoundaryInside N.spanningCompletion.selection
      N.completedContour.cycle e.val target := by
    change N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target))) e.val
    rw [vertex]
    exact N.spanningCompletion.parents.ancestor_refl e.val
  obtain ⟨region, a, b, ne, first, last, enters, leaves, stable, inside⟩ :=
    exists_finRotate_subinterval
      (C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val)
      O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
      (finRotate (N.completedContour.length + 1) O.enter) target different O.enters.2
      target_inside (Or.inl rfl)
  refine ⟨⟨region, a, b, ne, enters, leaves, stable, inside, ?_⟩, first, last⟩
  rw [first, last, O.entrance_next_vertex, vertex]

/-- The remaining suffix to the parent's exit is also a genuine internal contour excursion. -/
theorem exists_exit_excursion (target : Fin (N.completedContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target)) = e.val)
    (different : target ≠ O.leave) :
    ∃ E : N.ContourExcursion e,
      finRotate (N.completedContour.length + 1) E.first = target ∧
      finRotate (N.completedContour.length + 1) E.last = O.leave := by
  have target_inside : C.SubtreeBoundaryInside N.spanningCompletion.selection
      N.completedContour.cycle e.val target := by
    change N.spanningCompletion.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex N.completedRetain (N.completedContour.cycle.point target))) e.val
    rw [vertex]
    exact N.spanningCompletion.parents.ancestor_refl e.val
  obtain ⟨region, a, b, ne, first, last, enters, leaves, stable, inside⟩ :=
    exists_finRotate_subinterval
      (C.SubtreeBoundaryInside N.spanningCompletion.selection N.completedContour.cycle e.val)
      O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
      target O.leave different target_inside O.inside (Or.inr rfl)
  refine ⟨⟨region, a, b, ne, enters, leaves, stable, inside, ?_⟩, first, last⟩
  rw [first, last, vertex, O.exit_vertex]

end Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening
