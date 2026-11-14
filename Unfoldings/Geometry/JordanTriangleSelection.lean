module

public import Unfoldings.Geometry.ConvexCellRegion
public import Unfoldings.Geometry.Triangle
public import Unfoldings.Topology.ClosedJordanDomain

/-! A mesh respecting a Jordan curve constructs the exact bounded region by whole triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleFamily

variable {I : Type*} [Finite I] (triangles : I → Triangle)

/-- Actual geometric interiors select the triangles; no region or disk certificate is input. -/
theorem jordanDomain_eq_selected_triangles {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J)
    (convex : Convex ℝ (⋃ i, (triangles i).carrier))
    (contains : J ⊆ ⋃ i, (triangles i).carrier)
    (avoids : ∀ i, Disjoint (interior (triangles i).carrier) J) :
    PlanarTopology.closedJordanDomain J =
      ⋃ i ∈ ConvexCellRegion.selected (fun i => (triangles i).carrier)
        (PlanarTopology.closedJordanDomain J), (triangles i).carrier := by
  have compact : IsCompact (⋃ i, (triangles i).carrier) :=
    isCompact_iUnion (fun i => (triangles i).compact_carrier)
  have enclosed := PlanarTopology.closedJordanDomain_subset_convex jordan compact convex contains
  apply ConvexCellRegion.eq_union_selected_cells _ _ isClosed_closure
    (PlanarTopology.regular_closedJordanDomain jordan)
    (fun i => (triangles i).compact_carrier.isClosed)
    (fun i => (triangles i).convex_carrier) (fun i => (triangles i).interior_nonempty)
    (interior_subset.trans enclosed)
  intro i
  change Disjoint (interior (triangles i).carrier)
    (frontier (PlanarTopology.closedJordanDomain J))
  rw [PlanarTopology.frontier_closedJordanDomain jordan]
  exact avoids i

omit [Finite I] in
/-- Every face incident at a point strictly inside the Jordan region is selected. -/
theorem jordanDomain_incident_triangle_selected {J : Set Plane} (i : I) {x : Plane}
    (inside : x ∈ interior (PlanarTopology.closedJordanDomain J))
    (incident : x ∈ (triangles i).carrier) :
    i ∈ ConvexCellRegion.selected (fun i => (triangles i).carrier)
      (PlanarTopology.closedJordanDomain J) :=
  ConvexCellRegion.selected_of_incident_interior _ _ i (triangles i).compact_carrier.isClosed
    (triangles i).convex_carrier (triangles i).interior_nonempty inside incident

end Unfoldings.TriangleFamily
