module

public import Unfoldings.Cap.VertexExcursionRestoration
public import Unfoldings.Topology.CyclicInternalIntervals

/-! All coincident copies of one original vertex agree after pruning, including rim roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Interior and rim vertices both admit an internal contour interval between any two copies. -/
theorem exists_vertex_excursion (e : C.Vertex Set.univ)
    (start finish : Fin (M.projectionContour.length + 1)) (distinct : start ≠ finish)
    (first : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) = e)
    (last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)) = e) :
    ∃ E : M.VertexContourExcursion e,
      (finRotate (M.projectionContour.length + 1) E.first = start ∧
        finRotate (M.projectionContour.length + 1) E.last = finish) ∨
      (finRotate (M.projectionContour.length + 1) E.first = finish ∧
        finRotate (M.projectionContour.length + 1) E.last = start) := by
  have exits : ∃ enter leave : Fin (M.projectionContour.length + 1), enter ≠ leave ∧
      (¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e enter ∧
        C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) enter)) ∧
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e leave ∧
        ¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) leave)) ∧
      ∀ i, i ≠ enter → i ≠ leave →
        (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e
          (finRotate (M.projectionContour.length + 1) i) ↔
            C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e i) := by
    by_cases root : e ∈ M.parents.roots
    · exact M.exists_oriented_root_subtree_exits e root
    · exact C.exists_oriented_subtree_exits M.selection M.roots_eq
        M.projectionContour.cycle M.projectionContour.closes M.projectionContour.covers e root
  obtain ⟨enter, leave, ne, enters, leaves, stable⟩ := exits
  have first_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e start := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start))) e
    rw [first]
    exact M.parents.ancestor_refl _
  have last_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e finish := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish))) e
    rw [last]
    exact M.parents.ancestor_refl _
  obtain ⟨region, a, b, different, ends, changes_a, changes_b, unchanged, inside⟩ :=
    exists_finRotate_internal_interval
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e)
      enter leave ne enters leaves stable start finish distinct first_inside last_inside
  have first_vertex : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) a))) = e := by
    rcases ends with ⟨x, _⟩ | ⟨x, _⟩
    · rw [x]; exact first
    · rw [x]; exact last
  have last_vertex : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
      (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) b))) = e := by
    rcases ends with ⟨_, y⟩ | ⟨_, y⟩
    · rw [y]; exact last
    · rw [y]; exact first
  exact ⟨⟨region, a, b, different, changes_a, changes_b, unchanged, inside,
    first_vertex, last_vertex⟩, ends⟩

namespace SectorFrameData

variable {M} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- Every actual contour contact over one original vertex is identified by pruning. -/
theorem contour_vertex_contacts_identified
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (start finish : Fin (M.projectionContour.length + 1))
    (labels : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) =
        C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)))
    (same : D.boundaryPosition (M.projectionContour.cycle.point start) =
      D.boundaryPosition (M.projectionContour.cycle.point finish)) :
    C.vertexForgetCuts M.retain_subset_curvedRetain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) =
    C.vertexForgetCuts M.retain_subset_curvedRetain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)) := by
  by_cases distinct : start = finish
  · rw [distinct]
  obtain ⟨E, ⟨x, y⟩ | ⟨x, y⟩⟩ := M.exists_vertex_excursion _ start finish distinct rfl labels.symm
  · have gap : D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first)) := by
      rw [x, y]; exact same.symm
    have identified := B.closing_vertex_excursion_endpoints_identified E budget gap
    rw [x, y] at identified
    exact identified.symm
  · have gap : D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first)) := by
      rw [x, y]; exact same
    have identified := B.closing_vertex_excursion_endpoints_identified E budget gap
    rw [x, y] at identified
    exact identified

end SectorFrameData
end Unfoldings.ConvexCap.SectorForest
