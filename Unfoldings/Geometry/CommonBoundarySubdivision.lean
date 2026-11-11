module

public import Unfoldings.Geometry.SegmentGraph
public import Unfoldings.Geometry.TriangleFrontier

/-!
# One shared subdivision of all edges in a finite triangle family

Each original triangle frontier is covered exactly by shared marked vertices
and whole graph edges contained in that frontier. The same global edge labels
serve both sides of any shared boundary, including original T-junctions.
No non-overlap assumption is required to construct this boundary subdivision.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Subdivide a finite collection of genuine triangle boundaries with one global edge system. -/
theorem exists_common_triangle_boundary_subdivision {I : Type*} [Finite I]
    (triangle : I → Triangle) :
    ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Plane),
      G.IsStraight ∧ G.carrier = ⋃ i, frontier (triangle i).carrier ∧
        ∀ i, ∀ x ∈ frontier (triangle i).carrier,
          (∃ v, G.vertex v = x) ∨
            ∃ e, Set.range (G.edge e) ⊆ frontier (triangle i).carrier ∧
              x ∈ Set.range (G.edge e) := by
  classical
  let segments := Set.range (fun p : I × Fin 3 =>
    ((triangle p.1).vertex p.2, (triangle p.1).vertex (Triangle.next p.2)))
  have finite : segments.Finite := Set.finite_range _
  obtain ⟨Vertex, Edge, G, straight, carrier, _refines, parent_cover⟩ :=
    exists_finite_embedded_straight_segment_graph_with_parent_cover segments finite
  have boundary_network : segmentCarrier segments = ⋃ i, frontier (triangle i).carrier := by
    ext x
    constructor
    · rintro member
      obtain ⟨pair, ⟨⟨i, e⟩, rfl⟩, on_segment⟩ := Set.mem_iUnion₂.mp member
      exact Set.mem_iUnion.mpr ⟨i, (triangle i).edge_subset_frontier e on_segment⟩
    · intro member
      obtain ⟨i, boundary⟩ := Set.mem_iUnion.mp member
      rw [(triangle i).frontier_eq_union_edges] at boundary
      obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp boundary
      exact Set.mem_iUnion₂.mpr ⟨_, ⟨(i, e), rfl⟩, on_edge⟩
  refine ⟨Vertex, Edge, G, straight, carrier.trans boundary_network, ?_⟩
  intro i x boundary
  rw [(triangle i).frontier_eq_union_edges] at boundary
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp boundary
  have parent_mem : ((triangle i).vertex e, (triangle i).vertex (Triangle.next e)) ∈ segments :=
    ⟨(i, e), rfl⟩
  rcases parent_cover _ parent_mem x on_edge with vertex | ⟨edge, included, member⟩
  · exact Or.inl vertex
  · exact Or.inr ⟨edge, included.trans ((triangle i).edge_subset_frontier e), member⟩

end Unfoldings
