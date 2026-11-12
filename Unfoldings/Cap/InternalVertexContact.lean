module

public import Unfoldings.Cap.ContourExcursionRestoration
public import Unfoldings.Topology.CyclicInternalIntervals

/-! Arbitrary coincident copies of an original interior vertex are identified after pruning. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {D : FacewiseDevelopment C M.retain}
  {e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}}
  (O : M.ParentBankOpening D e)

include O in
/-- Any two distinct contour copies over the child bound an actual internal excursion,
with the orientation chosen to remain inside its descendant region. -/
theorem exists_internal_excursion (start finish : Fin (M.projectionContour.length + 1))
    (distinct : start ≠ finish)
    (first : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) = e.val)
    (last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)) = e.val) :
    ∃ E : M.ContourExcursion e,
      (finRotate (M.projectionContour.length + 1) E.first = start ∧
        finRotate (M.projectionContour.length + 1) E.last = finish) ∨
      (finRotate (M.projectionContour.length + 1) E.first = finish ∧
        finRotate (M.projectionContour.length + 1) E.last = start) := by
  have first_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e.val start := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start))) e.val
    rw [first]
    exact M.parents.ancestor_refl _
  have last_inside : C.SubtreeBoundaryInside M.selection
      M.projectionContour.cycle e.val finish := by
    change M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish))) e.val
    rw [last]
    exact M.parents.ancestor_refl _
  obtain ⟨region, a, b, ne, ends, enters, leaves, stable, inside⟩ :=
    exists_finRotate_internal_interval
      (C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e.val)
      O.enter O.leave O.enter_ne_leave O.enters O.leaves O.stable
      start finish distinct first_inside last_inside
  have same_vertex :
      C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) a))) =
      C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex M.retain
        (M.projectionContour.cycle.point (finRotate (M.projectionContour.length + 1) b))) := by
    rcases ends with ⟨x, y⟩ | ⟨x, y⟩
    · rw [x, y, first, last]
    · rw [x, y, first, last]
  exact ⟨⟨region, a, b, ne, enters, leaves, stable, inside, same_vertex⟩, ends⟩

end Unfoldings.ConvexCap.SectorForest.ParentBankOpening

namespace Unfoldings.ConvexCap.SectorForest.SectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C M.retain}
  (B : M.SectorFrameData positive small D)

include B in
/-- This handles arbitrary branch copies, rather than only the two child endpoints
of one parent seam. Flat selected subtrees are restored in the actual intrinsic quotient. -/
theorem internal_contour_vertex_contacts_identified
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (start finish : Fin (M.projectionContour.length + 1))
    (first : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) = e.val)
    (last : C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)) = e.val)
    (same : D.boundaryPosition (M.projectionContour.cycle.point start) =
      D.boundaryPosition (M.projectionContour.cycle.point finish)) :
    C.vertexForgetCuts M.retain_subset_curvedRetain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point start)) =
    C.vertexForgetCuts M.retain_subset_curvedRetain
      (C.boundaryEndVertex M.retain (M.projectionContour.cycle.point finish)) := by
  by_cases distinct : start = finish
  · rw [distinct]
  obtain ⟨E, ⟨x, y⟩ | ⟨x, y⟩⟩ :=
    (M.parentBankOpening D e).exists_internal_excursion start finish distinct first last
  · have gap : D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first)) := by
      rw [x, y]
      exact same.symm
    have identified := B.closing_excursion_endpoints_identified E budget gap
    rw [x, y] at identified
    exact identified.symm
  · have gap : D.boundaryPosition (M.projectionContour.cycle.point
        (finRotate (M.projectionContour.length + 1) E.last)) =
        D.boundaryPosition (M.projectionContour.cycle.point
          (finRotate (M.projectionContour.length + 1) E.first)) := by
      rw [x, y]
      exact same
    have identified := B.closing_excursion_endpoints_identified E budget gap
    rw [x, y] at identified
    exact identified

end Unfoldings.ConvexCap.SectorForest.SectorFrameData
