module

public import Unfoldings.Geometry.ConvexPolygonCover
public import Unfoldings.Geometry.SegmentGraph

/-!
# Actual finite triangle partitions of compact convex polygons

First subdivide all boundary segment intersections and overlaps. The resulting
embedded straight boundary graph supplies disjoint open edges, and coning them
to an interior center gives genuine triangles with disjoint interiors and exact
coverage. This theorem does not yet package a conforming triangle complex.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace FiniteEmbeddedGraph

variable {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge Plane)

theorem IsStraight.range_edge (straight : G.IsStraight) (e : Edge) :
    Set.range (G.edge e) = segment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)) := by
  rw [segment_eq_image_lineMap]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, t.property, (straight e t).symm⟩
  · rintro ⟨t, member, equal⟩
    exact ⟨⟨t, member⟩, (straight e ⟨t, member⟩).trans equal⟩

end FiniteEmbeddedGraph

/-- Cone a genuine straight embedded boundary graph to an interior center. -/
theorem exists_triangle_partition_of_convex_boundary_graph {S : Set Plane}
    (compact : IsCompact S) (convex : Convex ℝ S) {q : Plane} (inside : q ∈ interior S)
    {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge Plane) (straight : G.IsStraight)
    (boundary : G.carrier = frontier S) :
    ∃ triangle : Edge → Triangle,
      S = ⋃ e, (triangle e).carrier ∧
      Pairwise (fun e f =>
        Disjoint (interior (triangle e).carrier) (interior (triangle f).carrier)) := by
  classical
  let := G.finite_vertices
  let := G.finite_edges
  let first : Vertex ⊕ Edge → Plane := Sum.elim G.vertex (fun e => G.vertex (G.left e))
  let last : Vertex ⊕ Edge → Plane := Sum.elim G.vertex (fun e => G.vertex (G.right e))
  have cover_cells (i : Vertex ⊕ Edge) : G.cell i = segment ℝ (first i) (last i) := by
    cases i with
    | inl v => exact (segment_same ℝ (G.vertex v)).symm
    | inr e => exact straight.range_edge G e
  have on_boundary (i : Vertex ⊕ Edge) : segment ℝ (first i) (last i) ⊆ frontier S := by
    rw [← cover_cells, ← boundary]
    exact Set.subset_iUnion (fun j => G.cell j) i
  have covers (p : Plane) (member : p ∈ frontier S) :
      ∃ i, p ∈ segment ℝ (first i) (last i) := by
    rw [← boundary] at member
    obtain ⟨i, in_cell⟩ := Set.mem_iUnion.mp member
    exact ⟨i, cover_cells i ▸ in_cell⟩
  have nonempty_index : Nonempty (Vertex ⊕ Edge) := by
    let x : Plane := q + EuclideanSpace.single 0 1
    have different : x ≠ q := by
      intro equal
      have coordinate := congrArg (fun p : Plane => p 0) equal
      simp only [x, PiLp.add_apply, EuclideanSpace.single,
        PiLp.single_apply, ite_true] at coordinate
      linarith
    obtain ⟨a, _positive, on_frontier⟩ :=
      exists_frontier_on_positive_ray compact convex inside different
    obtain ⟨i, _member⟩ := covers _ on_frontier
    exact ⟨i⟩
  let := nonempty_index
  have edge_boundary (e : Edge) :
      segment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)) ⊆ frontier S := on_boundary (.inr e)
  let triangle (e : Edge) := convexBoundaryTriangle compact convex inside
    (G.vertex_injective.ne (straight.endpoints_ne e)) (edge_boundary e)
  refine ⟨triangle, ?_, ?_⟩
  · have cover := polygonFanTriangle_cover compact convex inside first last on_boundary covers
    apply Set.Subset.antisymm _ (Set.iUnion_subset (fun e =>
      convexBoundaryTriangle_subset compact convex inside
        (G.vertex_injective.ne (straight.endpoints_ne e)) (edge_boundary e)))
    intro p member
    rw [cover] at member
    obtain ⟨⟨i, genuine⟩, in_triangle⟩ := Set.mem_iUnion.mp member
    cases i with
    | inl v => exact (genuine rfl).elim
    | inr e => exact Set.mem_iUnion.mpr ⟨e, in_triangle⟩
  · intro e f different
    apply convexBoundaryTriangle_disjoint compact convex inside
      (G.vertex_injective.ne (straight.endpoints_ne e)) (edge_boundary e)
      (G.vertex_injective.ne (straight.endpoints_ne f)) (edge_boundary f)
    rw [← straight.open_edge_image e, ← straight.open_edge_image f]
    exact G.disjoint_open_edges e f different

/-- A finite segment rim suffices to construct a genuine nonoverlapping triangle partition. -/
theorem exists_finite_triangle_partition_of_convex_polygon {S : Set Plane}
    (compact : IsCompact S) (convex : Convex ℝ S) (nonempty : (interior S).Nonempty)
    (edges : Set (Plane × Plane)) (finite : edges.Finite)
    (boundary : frontier S = segmentCarrier edges) :
    ∃ (I : Type) (_ : Finite I) (triangle : I → Triangle),
      S = ⋃ i, (triangle i).carrier ∧
      Pairwise (fun i j =>
        Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)) := by
  obtain ⟨Vertex, Edge, G, straight, carrier, _parents⟩ :=
    exists_finite_embedded_straight_segment_graph edges finite
  obtain ⟨q, inside⟩ := nonempty
  obtain ⟨triangle, covers, separated⟩ := exists_triangle_partition_of_convex_boundary_graph
    compact convex inside G straight (carrier.trans boundary.symm)
  exact ⟨Edge, G.finite_edges, triangle, covers, separated⟩

end Unfoldings
