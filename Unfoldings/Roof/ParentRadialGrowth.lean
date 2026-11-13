module

public import Unfoldings.Roof.SectorForestGeometry
public import Unfoldings.Geometry.ThreeSectorRays
public import Unfoldings.Geometry.RadialSegment

/-! Every selected parent edge strictly increases source distance along its entire length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

theorem parent_radial_outward (positive : 0 < t) (small : t < 1)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    0 ≤ inner ℝ (K.projectedVertex e.val - origin)
      (K.projectedVertex (M.parents.parent e.val) - K.projectedVertex e.val) := by
  have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  have position := M.iterate_position positive.le small e.val internal 0
  have direction := strictThreeSector_subset_closed t _ (M.direction e.val e.property)
  exact inner_nonneg_of_inDirectionWedge
    (threeSector_banks_inner_pos positive small (K.sourceSectorLabel t origin e.val)).le
    (inDirectionWedge_of_closedThreeSector positive.le small _ position)
    (inDirectionWedge_of_closedThreeSector positive.le small _ direction)

/-- The selected edge is genuinely nonconstant in the actual cap projection. -/
theorem projected_parent_ne
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    K.projectedVertex e.val ≠ K.projectedVertex (M.parents.parent e.val) := by
  intro equal
  have vertices := K.projectedVertex_injective equal
  have ascending := M.parents.ascending e.val e.property
  rw [← vertices] at ascending
  exact (lt_irrefl _ ascending)

/-- Strict radial progress holds for all ordered parameters, including shared subdivision points. -/
theorem parent_segment_strict_radial (positive : 0 < t) (small : t < 1)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    {a b : ℝ} (nonnegative : 0 ≤ a) (ordered : a < b) :
    dist (origin)
        (AffineMap.lineMap (K.projectedVertex e.val)
          (K.projectedVertex (M.parents.parent e.val)) a) <
      dist (origin)
        (AffineMap.lineMap (K.projectedVertex e.val)
          (K.projectedVertex (M.parents.parent e.val)) b) :=
  dist_lineMap_lt_of_inner_nonneg _ _ _ (M.parent_radial_outward positive small e)
    (M.projected_parent_ne e) nonnegative ordered

theorem parent_source_distance_lt (positive : 0 < t) (small : t < 1)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    dist (origin) (K.projectedVertex e.val) <
      dist (origin) (K.projectedVertex (M.parents.parent e.val)) := by
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    M.parent_segment_strict_radial positive small e (a := 0) (b := 1) le_rfl zero_lt_one

end Unfoldings.ConvexRoof.SectorForest
