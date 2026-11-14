module

public import Unfoldings.Geometry.StraightGraph

/-! Link-oriented segments inherit vertex avoidance and separation from straight graphs. -/

@[expose] public section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {G : FiniteEmbeddedGraph V E X} (straight : G.IsStraight)

include straight

theorem IsStraight.openSegment_eq_edge_image {e : E} {a b : V} (link : G.graph.IsLink e a b) :
    openSegment ℝ (G.vertex a) (G.vertex b) = G.edge e '' Set.Ioo (0 : unitInterval) 1 := by
  rw [straight.open_edge_image]
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact openSegment_symm ℝ _ _

theorem IsStraight.openSegment_avoids_vertices {e : E} {a b v : V}
    (link : G.graph.IsLink e a b) : G.vertex v ∉ openSegment ℝ (G.vertex a) (G.vertex b) := by
  rw [straight.openSegment_eq_edge_image link]
  rintro ⟨t, ht, equal⟩
  exact G.edge_avoids_vertices e t ht.1 ht.2 v equal

theorem IsStraight.openSegments_disjoint {e d : E} {a b c f : V} (different : e ≠ d)
    (first : G.graph.IsLink e a b) (last : G.graph.IsLink d c f) :
    Disjoint (openSegment ℝ (G.vertex a) (G.vertex b))
      (openSegment ℝ (G.vertex c) (G.vertex f)) := by
  rw [straight.openSegment_eq_edge_image first, straight.openSegment_eq_edge_image last]
  exact G.disjoint_open_edges e d different

end Unfoldings.FiniteEmbeddedGraph
