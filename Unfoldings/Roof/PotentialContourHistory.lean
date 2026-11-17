module

public import Unfoldings.Roof.PotentialCutDisk
public import Unfoldings.Complex.SupportedContourNeighbors

/-! Potential-selected forests construct complete contour histories with flat unused roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)

/-- All original rim vertices are marked roots; unused interior roots may also occur. -/
theorem boundary_roots : C.relativeCutRoots Set.univ ⊆ R.parents.roots := by
  intro v boundary
  exact (Set.ext_iff.mp R.roots_eq v).mpr (Or.inl boundary)

/-- A curvature-covering actual cut forest has zero curvature at every marked root,
including every unused interior subdivision vertex. -/
theorem root_curvature_eq_zero
    (covered : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      K.projectedVertex v ∈ cuts) (v : C.Vertex Set.univ) (root : v ∈ R.parents.roots) :
    C.interiorAngularDefect Set.univ v = 0 := by
  classical
  rcases (Set.ext_iff.mp R.roots_eq v).mp root with boundary | outside
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary]
  · have not_positive : ¬ 0 < C.interiorAngularDefect Set.univ v :=
      fun positive => outside (covered v positive)
    exact le_antisymm (not_lt.mp not_positive) (K.interiorCurvature_nonneg v)

variable (Q : C.BoundaryContour R.retain)

/-- Processing the original cut contour reaches every original fine vertex, including
the isolated flat roots that do not appear on that contour. -/
theorem contour_history_complete :
    ((R.parents.initialFrontier).run (C.selectedContourSeeds R.selection Q)).processed = Set.univ :=
  C.initial_run_selectedContourSeeds_of_supported_roots R.selection Q

/-- Original contour processing charges exactly the actual roof curvature. No auxiliary
cut through a flat unused vertex or supplied first-contact schedule is required. -/
theorem contour_history_curvature
    (covered : ∀ v : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ v →
      K.projectedVertex v ∈ cuts) :
    (((R.parents.initialFrontier).history (C.selectedContourSeeds R.selection Q)).map
      (fun v => C.interiorAngularDefect Set.univ v.val)).sum =
        C.totalInteriorAngularDefect Set.univ :=
  C.sum_initial_history_selectedContourSeeds_of_zero_roots R.selection Q
    (fun v => C.interiorAngularDefect Set.univ v) (R.root_curvature_eq_zero covered)

/-- The actual next fresh source is reached along its original selected parent seam. -/
theorem fresh_contour_parent (i : Fin Q.length)
    (fresh : C.contourOriginalVertex R.selection Q i.succ ∉
      (C.contourFrontier R.selection Q i.succ).processed) :
    R.parents.parent (C.contourOriginalVertex R.selection Q i.succ) =
      C.contourOriginalVertex R.selection Q i.castSucc :=
  C.fresh_contour_parent_of_boundary_roots R.selection R.boundary_roots Q i fresh

/-- A rim-started actual contour has at most one fresh selected seam at every step. -/
theorem contour_contactTime_le_one
    (starts : C.contourOriginalVertex R.selection Q 0 ∈ R.parents.roots)
    (i : Fin (Q.length + 1)) :
    (C.contourFrontier R.selection Q i).contactTime (C.contourOriginalVertex R.selection Q i) ≤ 1 :=
  C.rim_contour_contactTime_le_one_of_boundary_roots R.selection R.boundary_roots Q starts i

end Unfoldings.ConvexRoof.PotentialCutForest
