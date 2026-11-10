module

public import Unfoldings.Cap.SectorDevelopment
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Complex.SelectedSubtreeAngles
public import Unfoldings.Complex.BoundaryContour

/-!
# Actual branching-subtree angles for the constructed cap forest

The cut-disk topology constructs a complete actual boundary contour. Its
subtree corner turns equal pi minus the sum of the actual descendant curvatures,
which is nonnegative and at most the cap's total curvature. A planar rotation
identity and the noncrossing argument remain separate proof obligations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The contour comes from the actual cut disk, with no planar separation premise. -/
def contour : C.BoundaryContour M.retain :=
  C.boundaryContourOfConnected M.retain
    (K.folding.boundaryGraph_connected_of_disk M.retain M.cutDisk)

/-- Curvature of the original vertices descending from the specified forest vertex. -/
def subtreeCurvature (e : C.Vertex Set.univ) : ℝ :=
  ∑ v ∈ M.parents.descendants e, C.interiorAngularDefect Set.univ v

theorem subtreeCurvature_nonneg (e : C.Vertex Set.univ) : 0 ≤ M.subtreeCurvature e :=
  Finset.sum_nonneg (fun v _ => K.interiorCurvature_nonneg v)

theorem subtreeCurvature_le_total (e : C.Vertex Set.univ) :
    M.subtreeCurvature e ≤ C.totalInteriorAngularDefect Set.univ :=
  K.sum_interiorAngularDefect_le_totalCurvature (M.parents.descendants e)

open scoped Classical in
/-- The count includes every actual cut vertex copy, including those created at branches. -/
theorem sum_subtree_copies (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    (∑ w : C.Vertex M.retain,
      if M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _) w) e then (1 : ℝ) else 0) =
        2 * (M.parents.descendants e).card - 1 :=
  C.sum_subtree_vertex_copies M.selection M.roots_eq
    M.contour.cycle M.contour.closes M.contour.covers e nonroot

open scoped Classical in
/-- The aggregate turns are the actual intrinsic angles of copies in the actual boundary order. -/
theorem contour_subtree_turn (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    (∑ i : Fin (M.contour.length + 1),
      if M.parents.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex M.retain (M.contour.cycle.point i))) e then
          C.totalAngle M.retain (C.boundaryEndVertex M.retain (M.contour.cycle.point i)) -
            Real.pi else 0) = Real.pi - M.subtreeCurvature e := by
  classical
  exact (C.sum_boundaryCycle_vertices M.retain M.contour.cycle M.contour.closes
    M.contour.covers M.all_vertices_boundary _).trans
      (C.sum_subtree_boundary_turn M.selection M.roots_eq
        M.contour.cycle M.contour.closes M.contour.covers e nonroot)

end Unfoldings.ConvexCap.SectorForest
