module

public import Unfoldings.Geometry.CommonTriangleRefinement
public import Unfoldings.Geometry.ClosedTriangleRadial
public import Unfoldings.Topology.EmbeddedEdgeIntersections

/-! Two refined triangles in one center fan meet only on shared radial edge segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.CommonTriangleRefinement

variable {I : Type*} {original : I → Triangle} (R : CommonTriangleRefinement original)

/-- Away from the center, a common fan point projects to one common actual base endpoint. -/
theorem same_parent_intersection_radial_endpoint (i : I)
    (e f : R.graph.SubdividedBoundaryEdge (S := (original i).carrier)) (different : e ≠ f)
    {p : Plane} (in_first : p ∈ (R.triangle ⟨i, e⟩).carrier)
    (in_last : p ∈ (R.triangle ⟨i, f⟩).carrier) (off_center : p ≠ R.center i) :
    ∃ v, (v = R.graph.left e.val ∨ v = R.graph.right e.val) ∧
      (v = R.graph.left f.val ∨ v = R.graph.right f.val) ∧
      p ∈ segment ℝ (R.center i) (R.graph.vertex v) := by
  obtain ⟨a, first_base, s, s_bounds, first_ray⟩ :=
    (R.triangle ⟨i, e⟩).point_on_opposite_edge_ray in_first off_center
  obtain ⟨b, last_base, t, t_bounds, last_ray⟩ :=
    (R.triangle ⟨i, f⟩).point_on_opposite_edge_ray in_last off_center
  have first_member : a ∈ Set.range (R.graph.edge e.val) := by
    rw [← R.base_edge ⟨i, e⟩]
    exact first_base
  have last_member : b ∈ Set.range (R.graph.edge f.val) := by
    rw [← R.base_edge ⟨i, f⟩]
    exact last_base
  have a_frontier := e.property first_member
  have b_frontier := f.property last_member
  change p = R.center i + s • (a - R.center i) at first_ray
  change p = R.center i + t • (b - R.center i) at last_ray
  have same : a = b := frontier_eq_of_radial_rays_meet (original i).convex_carrier
    (R.center_inside i) a_frontier b_frontier s_bounds.1 t_bounds.1
      (first_ray.symm.trans last_ray)
  obtain ⟨v, at_v, first_endpoint, last_endpoint⟩ :=
    R.graph.distinct_edges_intersection_endpoints
      (fun equal => different (Subtype.ext equal)) first_member (same.symm ▸ last_member)
  refine ⟨v, first_endpoint, last_endpoint, ?_⟩
  have on_radial := lineMap_mem_segment ℝ (R.center i) a ⟨s_bounds.1.le, s_bounds.2⟩
  rw [AffineMap.lineMap_apply_module', add_comm, ← first_ray, ← at_v] at on_radial
  exact on_radial

/-- Every radial segment from the center to a base endpoint is a full refined triangle edge. -/
theorem radial_endpoint_edge (i : I)
    (e : R.graph.SubdividedBoundaryEdge (S := (original i).carrier)) {v : R.Vertex}
    (endpoint : v = R.graph.left e.val ∨ v = R.graph.right e.val) :
    ∃ edge : Fin 3, (R.triangle ⟨i, e⟩).edge edge =
      segment ℝ (R.center i) (R.graph.vertex v) := by
  rcases endpoint with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, segment_symm ℝ _ _⟩

/-- A noncentral intersection in one fan lies on a full edge shared by the two triangles. -/
theorem same_parent_intersection_shared_edge (i : I)
    (e f : R.graph.SubdividedBoundaryEdge (S := (original i).carrier)) (different : e ≠ f)
    {p : Plane} (in_first : p ∈ (R.triangle ⟨i, e⟩).carrier)
    (in_last : p ∈ (R.triangle ⟨i, f⟩).carrier) (off_center : p ≠ R.center i) :
    ∃ a b : Fin 3, (R.triangle ⟨i, e⟩).edge a = (R.triangle ⟨i, f⟩).edge b ∧
      p ∈ (R.triangle ⟨i, e⟩).edge a := by
  obtain ⟨v, first, last, member⟩ :=
    R.same_parent_intersection_radial_endpoint i e f different in_first in_last off_center
  obtain ⟨a, first_edge⟩ := R.radial_endpoint_edge i e first
  obtain ⟨b, last_edge⟩ := R.radial_endpoint_edge i f last
  exact ⟨a, b, first_edge.trans last_edge.symm, first_edge.symm ▸ member⟩

end Unfoldings.CommonTriangleRefinement
