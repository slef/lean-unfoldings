module

public import Unfoldings.Roof.ContourExcursion
public import Unfoldings.Topology.CyclicSubintervals

/-! Construct actual contour prefixes and suffixes between developed copies of a branch vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
  (O : M.ParentBankOpening D e)

theorem entrance_next_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) O.enter))) =
        e.val := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex M.retain
    M.projectionContour.cycle M.projectionContour.closes O.enter)
  change C.boundaryEndVertex M.retain
    (C.boundaryTurn M.retain (M.projectionContour.cycle.point O.enter)) =
      C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) O.enter)) at next
  rw [← next]
  exact (C.selected_parent_bank_enters M.selection e.val e.property
    (M.projectionContour.cycle.point O.enter) O.side O.first_named O.outside).2

theorem exit_next_vertex :
    C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) O.leave))) =
        M.parents.parent e.val := by
  have next := congrArg Subtype.val (C.boundaryCycle_next_vertex M.retain
    M.projectionContour.cycle M.projectionContour.closes O.leave)
  change C.boundaryEndVertex M.retain
    (C.boundaryTurn M.retain (M.projectionContour.cycle.point O.leave)) =
      C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) O.leave)) at next
  rw [← next]
  exact (C.selected_parent_bank_leaves M.selection e.val e.property
    (M.projectionContour.cycle.point O.leave) (!O.side) O.last_named O.inside).2

/-- Every other copy of the child vertex is reached by a genuine contour prefix inside its
descendant region. The prefix starts immediately after the parent's entrance bank. -/
theorem exists_entrance_excursion (target : Fin (M.projectionContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point target)) = e.val)
    (different : finRotate (M.projectionContour.length + 1) O.enter ≠ target) :
    ∃ E : M.ContourExcursion e,
      finRotate (M.projectionContour.length + 1) E.first =
        finRotate (M.projectionContour.length + 1) O.enter ∧
      finRotate (M.projectionContour.length + 1) E.last = target := by
  have target_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e.val target := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point target))) e.val
    rw [vertex]
    exact M.parents.ancestor_refl e.val
  obtain ⟨region, a, b, ne, first, last, enters, leaves, stable, inside⟩ :=
    exists_finRotate_subinterval
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val)
      O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
      (finRotate (M.projectionContour.length + 1) O.enter) target different O.enters.2
      target_inside (Or.inl rfl)
  refine ⟨⟨region, a, b, ne, enters, leaves, stable, inside, ?_⟩, first, last⟩
  rw [first, last, O.entrance_next_vertex, vertex]

/-- The remaining suffix to the parent's exit is also a genuine internal contour excursion. -/
theorem exists_exit_excursion (target : Fin (M.projectionContour.length + 1))
    (vertex : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point target)) = e.val)
    (different : target ≠ O.leave) :
    ∃ E : M.ContourExcursion e,
      finRotate (M.projectionContour.length + 1) E.first = target ∧
      finRotate (M.projectionContour.length + 1) E.last = O.leave := by
  have target_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e.val target := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point target))) e.val
    rw [vertex]
    exact M.parents.ancestor_refl e.val
  obtain ⟨region, a, b, ne, first, last, enters, leaves, stable, inside⟩ :=
    exists_finRotate_subinterval
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val)
      O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
      target O.leave different target_inside O.inside (Or.inr rfl)
  refine ⟨⟨region, a, b, ne, enters, leaves, stable, inside, ?_⟩, first, last⟩
  rw [first, last, vertex, O.exit_vertex]

end Unfoldings.ConvexRoof.SectorForest.ParentBankOpening
