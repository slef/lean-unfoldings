module

public import Unfoldings.Geometry.BoundaryHalfplanes
public import Unfoldings.Geometry.ConvexRayBoundary
public import Unfoldings.Geometry.TriangleRadial
public import Unfoldings.Geometry.RayAvoidance

/-!
# Genuine center triangles of a compact convex polygon

An actual boundary segment and an interior center determine a nondegenerate
triangle. Interior points of distinct such triangles cannot coincide when the
original open boundary segments are disjoint. This is geometry for subsequent
conforming triangulations, without identifying edges or assuming manifold data.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {S : Set Plane} (compact : IsCompact S) (convex : Convex ℝ S)
  {q a b : Plane} (inside : q ∈ interior S) (different : a ≠ b)
  (boundary : segment ℝ a b ⊆ frontier S)

def convexBoundaryTriangle : Triangle where
  vertex := ![q, a, b]
  nondegenerate := by
    change orient q a b ≠ 0
    rw [← orient_cyclic q a b]
    exact orient_ne_zero_of_boundary_segment convex compact.isClosed inside different boundary

theorem convexBoundaryTriangle_subset :
    (convexBoundaryTriangle compact convex inside different boundary).carrier ⊆ S := by
  apply convexHull_min _ convex
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact interior_subset inside
  · exact compact.isClosed.frontier_subset (boundary (left_mem_segment ℝ a b))
  · exact compact.isClosed.frontier_subset (boundary (right_mem_segment ℝ a b))

/-- The actual opposite-edge point is unique along an interior-center ray. -/
theorem convexBoundaryTriangle_ray_endpoint_unique
    {c d x : Plane} (other_different : c ≠ d)
    (other_boundary : segment ℝ c d ⊆ frontier S)
    (first : x ∈ interior (convexBoundaryTriangle compact convex inside different boundary).carrier)
    (last : x ∈ interior
      (convexBoundaryTriangle compact convex inside other_different other_boundary).carrier) :
    ∃ z, z ∈ openSegment ℝ a b ∧ z ∈ openSegment ℝ c d := by
  obtain ⟨z, first_edge, s, s_bounds, first_ray⟩ :=
    Triangle.interior_point_on_opposite_edge_ray
      (convexBoundaryTriangle compact convex inside different boundary) first
  obtain ⟨w, last_edge, t, t_bounds, last_ray⟩ :=
    Triangle.interior_point_on_opposite_edge_ray
      (convexBoundaryTriangle compact convex inside other_different other_boundary) last
  change x = q + s • (z - q) at first_ray
  change x = q + t • (w - q) at last_ray
  have first_frontier := boundary (openSegment_subset_segment ℝ a b first_edge)
  have last_frontier := other_boundary (openSegment_subset_segment ℝ c d last_edge)
  have same : z = w := frontier_eq_of_radial_rays_meet convex inside first_frontier last_frontier
    s_bounds.1 t_bounds.1 (first_ray.symm.trans last_ray)
  exact ⟨z, first_edge, same ▸ last_edge⟩

/-- Disjoint open boundary edges give center triangles with disjoint interiors. -/
theorem convexBoundaryTriangle_disjoint
    {c d : Plane} (other_different : c ≠ d)
    (other_boundary : segment ℝ c d ⊆ frontier S)
    (edges_disjoint : Disjoint (openSegment ℝ a b) (openSegment ℝ c d)) :
    Disjoint (interior (convexBoundaryTriangle compact convex inside different boundary).carrier)
      (interior
        (convexBoundaryTriangle compact convex inside other_different other_boundary).carrier) := by
  apply Set.disjoint_left.mpr
  intro x first last
  obtain ⟨z, in_first, in_last⟩ := convexBoundaryTriangle_ray_endpoint_unique compact convex
    inside different boundary other_different other_boundary first last
  exact Set.disjoint_left.mp edges_disjoint in_first in_last

end Unfoldings
