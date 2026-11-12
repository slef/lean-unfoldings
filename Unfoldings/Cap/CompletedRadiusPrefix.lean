module

public import Unfoldings.Cap.CompletedRootPathSupport
public import Unfoldings.Geometry.ChainRadiusCrossing

/-! Actual outward cut paths reach a prescribed radius before leaving the controlled ball. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)

theorem completedRootPath_radialFrom (outward : N.Outward) {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts) : (N.completedRootPath w).RadialFrom source 0 := by
  intro i _
  exact (monotone_dist_lineMap_iff _ _ _).mpr (N.completedRootPath_outward outward member i)

theorem completedRootPath_last_frontier (w : C.Vertex Set.univ) :
    (N.completedRootPath w).vertex (Fin.last (N.spanningCompletion.parents.distanceToRoot w)) ∈
      frontier K.footprint := by
  apply (K.projectedVertex_mem_frontier_iff _).mpr
  exact (Set.ext_iff.mp N.spanningCompletion.roots_eq _).mp
    (N.spanningCompletion.parents.iterate_distanceToRoot_mem w)

/-- Only the real outward path is used. The enclosing-ball hypothesis keeps its
chosen finite prefix away from the actual cap boundary. -/
theorem completedRootPath_exists_radius_prefix (outward : N.Outward) {w : C.Vertex Set.univ}
    (member : K.projectedVertex w ∈ cuts) (radius : ℝ)
    (start : dist source (K.projectedVertex w) < radius)
    (deep : Metric.closedBall source radius ⊆ interior K.footprint) :
    ∃ i : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      dist source ((N.completedRootPath w).point i s) = radius ∧
      (∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w + 1), j.val ≤ i.val →
        dist source ((N.completedRootPath w).vertex j) ≤ radius) ∧
      ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∀ r : unitInterval,
        PolygonalChain.Before j r i s →
          dist source ((N.completedRootPath w).point j r) ≤ radius := by
  have finish : radius < dist source ((N.completedRootPath w).vertex
      (Fin.last (N.spanningCompletion.parents.distanceToRoot w))) := by
    by_contra not_beyond
    have near := le_of_not_gt not_beyond
    exact (N.completedRootPath_last_frontier w).2
      (deep (by simpa only [Metric.mem_closedBall, dist_comm] using near))
  exact PolygonalChain.RadialFrom.exists_radius_prefix _
    (N.completedRootPath_radialFrom outward member) radius start finish.le

end Unfoldings.ConvexCap.RadialCutForest
