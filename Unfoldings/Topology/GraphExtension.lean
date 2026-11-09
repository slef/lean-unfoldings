module

public import Unfoldings.Topology.FiniteEmbeddedGraph
public import Unfoldings.Topology.QuotientRetraction

/-!
# Continuous maps out of finite embedded graphs

Assign vertex values and continuous edge maps agreeing at their endpoints.
The actual finite compact interval presentation is a quotient onto the graph
carrier, so these assignments descend continuously. Loop endpoints and all
parallel edges are handled by the same proved fiber compatibility.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
  (G : FiniteEmbeddedGraph Vertex Edge X)

theorem exists_continuous_extension (vertices : Vertex → Y) (edges : Edge → C(unitInterval, Y))
    (zero : ∀ e, edges e 0 = vertices (G.left e))
    (one : ∀ e, edges e 1 = vertices (G.right e)) :
    ∃ F : C(G.carrier, Y),
      (∀ v, F ⟨G.vertex v, G.mem_carrier_vertex v⟩ = vertices v) ∧
      ∀ e t, F ⟨G.edge e t, G.mem_carrier_edge e t⟩ = edges e t := by
  classical
  have edge_vertex (e : Edge) (t : unitInterval) (v : Vertex)
      (equal : G.edge e t = G.vertex v) : edges e t = vertices v := by
    by_cases at_zero : t = 0
    · have same := G.vertex_injective ((G.edge_zero e).symm.trans (at_zero ▸ equal))
      rw [at_zero, zero, same]
    by_cases at_one : t = 1
    · have same := G.vertex_injective ((G.edge_one e).symm.trans (at_one ▸ equal))
      rw [at_one, one, same]
    exact ((G.edge_avoids_vertices e t (bot_lt_iff_ne_bot.mpr at_zero)
      (lt_top_iff_ne_top.mpr at_one) v) equal).elim
  have edge_edge (e f : Edge) (t s : unitInterval)
      (equal : G.edge e t = G.edge f s) : edges e t = edges f s := by
    by_cases at_zero : t = 0
    · have target : G.edge f s = G.vertex (G.left e) := by
        rw [← equal, at_zero, G.edge_zero]
      rw [at_zero, zero, edge_vertex f s (G.left e) target]
    by_cases at_one : t = 1
    · have target : G.edge f s = G.vertex (G.right e) := by
        rw [← equal, at_one, G.edge_one]
      rw [at_one, one, edge_vertex f s (G.right e) target]
    by_cases last_zero : s = 0
    · have target : G.edge e t = G.vertex (G.left f) := by rw [equal, last_zero, G.edge_zero]
      rw [last_zero, zero, edge_vertex e t (G.left f) target]
    by_cases last_one : s = 1
    · have target : G.edge e t = G.vertex (G.right f) := by rw [equal, last_one, G.edge_one]
      rw [last_one, one, edge_vertex e t (G.right f) target]
    have ht : t ∈ Set.Ioo (0 : unitInterval) 1 :=
      ⟨bot_lt_iff_ne_bot.mpr at_zero, lt_top_iff_ne_top.mpr at_one⟩
    have hs : s ∈ Set.Ioo (0 : unitInterval) 1 :=
      ⟨bot_lt_iff_ne_bot.mpr last_zero, lt_top_iff_ne_top.mpr last_one⟩
    by_cases same : e = f
    · subst f
      exact congrArg (edges e) (G.edge_injective e ht hs equal)
    · exact (Set.disjoint_left.mp (G.disjoint_open_edges e f same)
        ⟨t, ht, rfl⟩ ⟨s, hs, equal.symm⟩).elim
  let := G.finite_vertices
  let := G.finite_edges
  let : TopologicalSpace Vertex := ⊥
  let : DiscreteTopology Vertex := ⟨rfl⟩
  let : TopologicalSpace Edge := ⊥
  let : DiscreteTopology Edge := ⟨rfl⟩
  let Domain := Vertex ⊕ (Edge × unitInterval)
  let evaluate : Domain → X := Sum.elim G.vertex (fun p => G.edge p.1 p.2)
  have continuous_evaluate : Continuous evaluate := continuous_sum_dom.mpr
    ⟨continuous_of_discreteTopology,
      continuous_prod_of_discrete_left.mpr (fun e => (G.edge e).continuous)⟩
  have member (x : Domain) : evaluate x ∈ G.carrier := by
    cases x with
    | inl v => exact G.mem_carrier_vertex v
    | inr p => exact G.mem_carrier_edge p.1 p.2
  let onto (x : Domain) : G.carrier := ⟨evaluate x, member x⟩
  have continuous_onto : Continuous onto := continuous_evaluate.subtype_mk _
  have surjective : Function.Surjective onto := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    cases i with
    | inl v => exact ⟨Sum.inl v, Subtype.ext hi.symm⟩
    | inr e =>
      obtain ⟨t, ht⟩ := hi
      exact ⟨Sum.inr (e, t), Subtype.ext ht⟩
  let value : Domain → Y := Sum.elim vertices (fun p => edges p.1 p.2)
  have continuous_value : Continuous value := continuous_sum_dom.mpr
    ⟨continuous_of_discreteTopology,
      continuous_prod_of_discrete_left.mpr (fun e => (edges e).continuous)⟩
  have compatible (a b : Domain) (equal : onto a = onto b) : value a = value b := by
    have images : evaluate a = evaluate b := congrArg Subtype.val equal
    cases a with
    | inl v =>
      cases b with
      | inl w => exact congrArg vertices (G.vertex_injective images)
      | inr p => exact (edge_vertex p.1 p.2 v images.symm).symm
    | inr p =>
      cases b with
      | inl w => exact edge_vertex p.1 p.2 w images
      | inr q => exact edge_edge p.1 q.1 p.2 q.2 images
  have quotient : Topology.IsQuotientMap onto :=
    Topology.IsQuotientMap.of_surjective_continuous surjective continuous_onto
  let F := quotientContinuousDesc onto quotient ⟨value, continuous_value⟩ compatible
  exact ⟨F, fun v => quotientContinuousDesc_apply onto quotient ⟨value, continuous_value⟩ compatible
    (Sum.inl v), fun e t => quotientContinuousDesc_apply onto quotient
      ⟨value, continuous_value⟩ compatible (Sum.inr (e, t))⟩

end Unfoldings.FiniteEmbeddedGraph
