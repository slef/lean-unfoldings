module

public import Unfoldings.Cap.MonotoneForest
public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Geometry.RadialChainPoints

/-!
# Actual finite angle-monotone paths in the selected cap forest

Every path ends at its first original boundary vertex. Its projected steps are
original selected seams in the same strict acute wedge. Radial monotonicity
holds throughout the closed edges and from arbitrary earlier edge points.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.MonotoneForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} (M : K.MonotoneForest t)

def rootPath (v : C.Vertex Set.univ) : PolygonalChain Plane (M.parents.distanceToRoot v) where
  vertex i := K.projectedVertex (M.parents.parent^[i.val] v)

@[simp] theorem rootPath_start (v : C.Vertex Set.univ) :
    (M.rootPath v).vertex 0 = K.projectedVertex v := rfl

theorem rootPath_end (v : C.Vertex Set.univ) :
    (M.rootPath v).vertex (Fin.last (M.parents.distanceToRoot v)) =
      K.projectedVertex (M.parents.root v) :=
  congrArg K.projectedVertex (M.parents.iterate_distanceToRoot_eq_root v)

theorem rootPath_edge (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    (M.rootPath v).edge i =
      K.projectedVertex (M.parents.parent (M.parents.parent^[i.val] v)) -
        K.projectedVertex (M.parents.parent^[i.val] v) := by
  change K.projectedVertex (M.parents.parent^[i.val + 1] v) -
    K.projectedVertex (M.parents.parent^[i.val] v) = _
  rw [Function.iterate_succ_apply']

theorem rootPath_directions (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    StrictQuadrant (quadrantShear t ((M.rootPath v).edge i)) := by
  rw [M.rootPath_edge]
  exact M.direction _ (M.parents.iterate_lt_distanceToRoot_not_mem v i.isLt)

theorem rootPath_angleMonotone (v : C.Vertex Set.univ) :
    (M.rootPath v).AngleMonotone (shearWedgeWidth t) :=
  (M.rootPath v).angleMonotone_of_sheared_quadrant t (M.rootPath_directions v)

theorem rootPath_radiallyMonotone (positive : 0 < t) (v : C.Vertex Set.univ) :
    (M.rootPath v).RadiallyMonotone :=
  (M.rootPath v).radiallyMonotone_of_sheared_quadrant positive (M.rootPath_directions v)

theorem rootPath_globallyRadiallyMonotone (positive : 0 < t) (v : C.Vertex Set.univ) :
    (M.rootPath v).GloballyRadiallyMonotone :=
  (M.rootPath_radiallyMonotone positive v).globallyRadiallyMonotone

/-- Each step names an actual original seam between precisely its two original vertex classes. -/
theorem rootPath_original_edge (v : C.Vertex Set.univ) (i : Fin (M.parents.distanceToRoot v)) :
    ∃ s : C.Seam, C.seamGraph.IsLink s (M.parents.parent^[i.val] v)
      (M.parents.parent^[i.val + 1] v) := by
  let source : {w : C.Vertex Set.univ // w ∉ M.parents.roots} :=
    ⟨M.parents.parent^[i.val] v, M.parents.iterate_lt_distanceToRoot_not_mem v i.isLt⟩
  refine ⟨M.selection.edge source, ?_⟩
  rw [Function.iterate_succ_apply']
  exact M.selection.link source

theorem rootPath_end_boundary (v : C.Vertex Set.univ) :
    C.IsBoundaryVertex Set.univ (M.parents.root v) := by
  have root := M.parents.root_mem v
  rwa [M.roots_eq] at root

end Unfoldings.ConvexCap.MonotoneForest
