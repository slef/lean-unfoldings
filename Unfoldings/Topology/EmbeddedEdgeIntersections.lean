module

public import Unfoldings.Topology.FiniteEmbeddedGraph

/-! Distinct edges of an actual embedded graph can meet only at shared named endpoints. -/

@[expose] public section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X : Type*} [TopologicalSpace X] (G : FiniteEmbeddedGraph Vertex Edge X)

theorem edge_eq_vertex_endpoint (e : Edge) (t : unitInterval) (v : Vertex)
    (same : G.edge e t = G.vertex v) : v = G.left e ∨ v = G.right e := by
  by_cases zero : t = 0
  · exact Or.inl ((G.vertex_injective ((G.edge_zero e).symm.trans (zero ▸ same))).symm)
  by_cases one : t = 1
  · exact Or.inr ((G.vertex_injective ((G.edge_one e).symm.trans (one ▸ same))).symm)
  exact ((G.edge_avoids_vertices e t
    (bot_lt_iff_ne_bot.mpr zero) (lt_top_iff_ne_top.mpr one) v) same).elim

/-- Distinct whole edge carriers meet only at vertices which are endpoints of both edges. -/
theorem distinct_edges_intersection_endpoints {e f : Edge} (different : e ≠ f) {x : X}
    (first : x ∈ Set.range (G.edge e)) (last : x ∈ Set.range (G.edge f)) :
    ∃ v, G.vertex v = x ∧ (v = G.left e ∨ v = G.right e) ∧
      (v = G.left f ∨ v = G.right f) := by
  obtain ⟨t, at_t⟩ := first
  obtain ⟨s, at_s⟩ := last
  by_cases zero : t = 0
  · have at_vertex : G.vertex (G.left e) = x := (G.edge_zero e).symm.trans (zero ▸ at_t)
    exact ⟨G.left e, at_vertex, Or.inl rfl,
      G.edge_eq_vertex_endpoint f s _ (at_s.trans at_vertex.symm)⟩
  by_cases one : t = 1
  · have at_vertex : G.vertex (G.right e) = x := (G.edge_one e).symm.trans (one ▸ at_t)
    exact ⟨G.right e, at_vertex, Or.inr rfl,
      G.edge_eq_vertex_endpoint f s _ (at_s.trans at_vertex.symm)⟩
  have interior_t : t ∈ Set.Ioo (0 : unitInterval) 1 :=
    ⟨bot_lt_iff_ne_bot.mpr zero, lt_top_iff_ne_top.mpr one⟩
  by_cases last_zero : s = 0
  · have at_vertex : G.edge e t = G.vertex (G.left f) := by
      rw [at_t, ← at_s, last_zero, G.edge_zero]
    exact (G.edge_avoids_vertices e t interior_t.1 interior_t.2 _ at_vertex).elim
  by_cases last_one : s = 1
  · have at_vertex : G.edge e t = G.vertex (G.right f) := by
      rw [at_t, ← at_s, last_one, G.edge_one]
    exact (G.edge_avoids_vertices e t interior_t.1 interior_t.2 _ at_vertex).elim
  have interior_s : s ∈ Set.Ioo (0 : unitInterval) 1 :=
    ⟨bot_lt_iff_ne_bot.mpr last_zero, lt_top_iff_ne_top.mpr last_one⟩
  exact (Set.disjoint_left.mp (G.disjoint_open_edges e f different)
    ⟨t, interior_t, at_t⟩ ⟨s, interior_s, at_s⟩).elim

end Unfoldings.FiniteEmbeddedGraph
