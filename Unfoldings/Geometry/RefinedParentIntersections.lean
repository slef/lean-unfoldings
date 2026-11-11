module

public import Unfoldings.Geometry.CommonTriangleRefinement
public import Unfoldings.Topology.EmbeddedEdgeIntersections

/-! Refined triangles in different old parents meet only on their global boundary bases. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Disjoint triangle interiors imply that their closed intersection lies on both frontiers. -/
theorem intersection_subset_frontiers (T U : Triangle)
    (separated : Disjoint (interior T.carrier) (interior U.carrier)) :
    T.carrier ∩ U.carrier ⊆ frontier T.carrier ∩ frontier U.carrier := by
  have closure_T := T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    T.interior_nonempty
  have closure_U := U.convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    U.interior_nonempty
  rw [T.compact_carrier.isClosed.closure_eq] at closure_T
  rw [U.compact_carrier.isClosed.closure_eq] at closure_U
  have first := separated.closure_left isOpen_interior
  have last := separated.closure_right isOpen_interior
  rw [closure_T] at first
  rw [closure_U] at last
  intro p member
  exact ⟨⟨subset_closure member.1, fun inside => Set.disjoint_left.mp last inside member.2⟩,
    ⟨subset_closure member.2, fun inside => Set.disjoint_left.mp first member.1 inside⟩⟩

end Unfoldings.Triangle

namespace Unfoldings.CommonTriangleRefinement

variable {I : Type*} {original : I → Triangle} (R : CommonTriangleRefinement original)
  (parents_separated : Pairwise (fun i j =>
    Disjoint (interior (original i).carrier) (interior (original j).carrier)))

include parents_separated in
/-- All contacts between distinct parent fans are contacts between their globally named bases. -/
theorem different_parent_intersection_bases {j k : R.Index} (different : j.1 ≠ k.1) :
    (R.triangle j).carrier ∩ (R.triangle k).carrier ⊆
      Set.range (R.graph.edge j.2.val) ∩ Set.range (R.graph.edge k.2.val) := by
  intro p member
  have parents := (original j.1).intersection_subset_frontiers (original k.1)
    (parents_separated different)
    ⟨R.triangle_subset j member.1, R.triangle_subset k member.2⟩
  exact ⟨R.parent_frontier_subset_base j ⟨member.1, parents.1⟩,
    R.parent_frontier_subset_base k ⟨member.2, parents.2⟩⟩

include parents_separated in
/-- If the base label agrees, the intersection is exactly the one entire shared base edge. -/
theorem different_parent_same_base {j k : R.Index} (different : j.1 ≠ k.1)
    (same_edge : j.2.val = k.2.val) :
    (R.triangle j).carrier ∩ (R.triangle k).carrier = Set.range (R.graph.edge j.2.val) := by
  apply Set.Subset.antisymm
  · exact (R.different_parent_intersection_bases parents_separated different).trans
      Set.inter_subset_left
  · intro p member
    have first : p ∈ (R.triangle j).edge 1 := R.base_edge j ▸ member
    have last : p ∈ (R.triangle k).edge 1 := by rw [R.base_edge, ← same_edge]; exact member
    exact ⟨(R.triangle j).edge_subset 1 first, (R.triangle k).edge_subset 1 last⟩

include parents_separated in
/-- Distinct base labels allow only their common named graph endpoints. -/
theorem different_parent_distinct_base {j k : R.Index} (different : j.1 ≠ k.1)
    (different_edges : j.2.val ≠ k.2.val) {p : Plane}
    (member : p ∈ (R.triangle j).carrier ∩ (R.triangle k).carrier) :
    ∃ v, R.graph.vertex v = p ∧
      (v = R.graph.left j.2.val ∨ v = R.graph.right j.2.val) ∧
      (v = R.graph.left k.2.val ∨ v = R.graph.right k.2.val) := by
  have bases := R.different_parent_intersection_bases parents_separated different member
  exact R.graph.distinct_edges_intersection_endpoints different_edges bases.1 bases.2

end Unfoldings.CommonTriangleRefinement
