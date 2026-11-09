module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Fintype.Sum

/-!
# Finite graphs embedded in a topological space

Vertices and edges have separate finite index types. An edge is a continuous
closed interval, injective in its interior; only its endpoints may coincide.
Open edges avoid every vertex and distinct open edges are disjoint. Thus loops
and parallel edges are allowed, with their geometric identifications recorded
explicitly. Complementary faces and rotation systems are separate data.

This module is independent of metric and unfolding geometry.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v w

structure FiniteEmbeddedGraph (Vertex : Type u) (Edge : Type v) (X : Type w)
    [TopologicalSpace X] where
  finite_vertices : Finite Vertex
  finite_edges : Finite Edge
  vertex : Vertex → X
  vertex_injective : Function.Injective vertex
  left : Edge → Vertex
  right : Edge → Vertex
  edge : Edge → C(unitInterval, X)
  edge_zero : ∀ e, edge e 0 = vertex (left e)
  edge_one : ∀ e, edge e 1 = vertex (right e)
  edge_injective : ∀ e, Set.InjOn (edge e) (Set.Ioo 0 1)
  edge_avoids_vertices : ∀ e t, 0 < t → t < 1 → ∀ v, edge e t ≠ vertex v
  disjoint_open_edges : ∀ e f, e ≠ f →
    Disjoint (edge e '' Set.Ioo 0 1) (edge f '' Set.Ioo 0 1)

namespace FiniteEmbeddedGraph

variable {Vertex : Type u} {Edge : Type v} {X : Type w} [TopologicalSpace X]
  (G : FiniteEmbeddedGraph Vertex Edge X)

def graph : Graph Vertex Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := (x = G.left e ∧ y = G.right e) ∨ (x = G.right e ∧ y = G.left e)
  isLink_symm := by
    intro e _
    constructor
    intro x y h
    exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y z t h k
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rcases k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp
  edge_mem_iff_exists_isLink := fun e => ⟨fun _ => ⟨G.left e, G.right e, Or.inl ⟨rfl, rfl⟩⟩,
    fun _ => Set.mem_univ e⟩
  left_mem_of_isLink := by
    intro e x y h
    exact Set.mem_univ x

/-- Forget loops and parallel-edge multiplicity only for reachability questions. -/
def adjacencyGraph : SimpleGraph Vertex where
  Adj x y := x ≠ y ∧ ∃ e, (x = G.left e ∧ y = G.right e) ∨ (x = G.right e ∧ y = G.left e)
  symm := by
    constructor
    intro x y ⟨different, e, link⟩
    exact ⟨different.symm, e, link.elim (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def cell : Vertex ⊕ Edge → Set X
  | .inl v => {G.vertex v}
  | .inr e => Set.range (G.edge e)

def anchor : Vertex ⊕ Edge → Vertex
  | .inl v => v
  | .inr e => G.left e

def carrier : Set X := ⋃ i, G.cell i

theorem mem_carrier_vertex (v : Vertex) : G.vertex v ∈ G.carrier :=
  Set.mem_iUnion.mpr ⟨Sum.inl v, rfl⟩

theorem mem_carrier_edge (e : Edge) (t : unitInterval) : G.edge e t ∈ G.carrier :=
  Set.mem_iUnion.mpr ⟨Sum.inr e, t, rfl⟩

theorem compact_cell (i : Vertex ⊕ Edge) : IsCompact (G.cell i) := by
  cases i with
  | inl v => exact isCompact_singleton
  | inr e => exact isCompact_range (G.edge e).continuous

theorem compact_carrier : IsCompact G.carrier := by
  let := G.finite_vertices
  let := G.finite_edges
  let := Fintype.ofFinite Vertex
  let := Fintype.ofFinite Edge
  exact isCompact_iUnion G.compact_cell

theorem endpoints_reachable (e : Edge) : G.adjacencyGraph.Reachable (G.left e) (G.right e) := by
  by_cases equal : G.left e = G.right e
  · rw [equal]
  · exact SimpleGraph.Adj.reachable ⟨equal, e, Or.inl ⟨rfl, rfl⟩⟩

theorem edge_vertex_reachable (e : Edge) (t : unitInterval) (v : Vertex)
    (equal : G.edge e t = G.vertex v) : G.adjacencyGraph.Reachable (G.left e) v := by
  by_cases zero : t = 0
  · have same := G.vertex_injective ((G.edge_zero e).symm.trans (zero ▸ equal))
    rw [same]
  by_cases one : t = 1
  · have same := G.vertex_injective ((G.edge_one e).symm.trans (one ▸ equal))
    rw [← same]
    exact G.endpoints_reachable e
  exact ((G.edge_avoids_vertices e t
    (bot_lt_iff_ne_bot.mpr zero) (lt_top_iff_ne_top.mpr one) v) equal).elim

theorem edges_intersection_reachable (e f : Edge) (t s : unitInterval)
    (equal : G.edge e t = G.edge f s) :
    G.adjacencyGraph.Reachable (G.left e) (G.left f) := by
  by_cases zero : s = 0
  · rw [zero, G.edge_zero] at equal
    exact G.edge_vertex_reachable e t (G.left f) equal
  by_cases one : s = 1
  · rw [one, G.edge_one] at equal
    exact (G.edge_vertex_reachable e t (G.right f) equal).trans (G.endpoints_reachable f).symm
  by_cases first_zero : t = 0
  · rw [first_zero, G.edge_zero] at equal
    exact (G.edge_vertex_reachable f s (G.left e) equal.symm).symm
  by_cases first_one : t = 1
  · rw [first_one, G.edge_one] at equal
    exact (G.endpoints_reachable e).trans (G.edge_vertex_reachable f s (G.right e) equal.symm).symm
  by_cases same : e = f
  · rw [same]
  have interior_t : t ∈ Set.Ioo (0 : unitInterval) 1 :=
    ⟨bot_lt_iff_ne_bot.mpr first_zero, lt_top_iff_ne_top.mpr first_one⟩
  have interior_s : s ∈ Set.Ioo (0 : unitInterval) 1 :=
    ⟨bot_lt_iff_ne_bot.mpr zero, lt_top_iff_ne_top.mpr one⟩
  exact (Set.disjoint_left.mp (G.disjoint_open_edges e f same)
    ⟨t, interior_t, rfl⟩ ⟨s, interior_s, equal.symm⟩).elim

theorem cells_intersection_reachable (i j : Vertex ⊕ Edge) {x : X}
    (hi : x ∈ G.cell i) (hj : x ∈ G.cell j) :
    G.adjacencyGraph.Reachable (G.anchor i) (G.anchor j) := by
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      have same := G.vertex_injective (hi.symm.trans hj)
      change G.adjacencyGraph.Reachable v w
      rw [same]
    | inr f =>
      obtain ⟨s, rfl⟩ := hj
      exact (G.edge_vertex_reachable f s v hi).symm
  | inr e =>
    obtain ⟨t, rfl⟩ := hi
    cases j with
    | inl w => exact G.edge_vertex_reachable e t w hj
    | inr f =>
      obtain ⟨s, equal⟩ := hj
      exact G.edges_intersection_reachable e f t s equal.symm

theorem connected_of_isConnected [T2Space X] (connected : IsConnected G.carrier) :
    G.adjacencyGraph.Connected := by
  classical
  let := G.finite_vertices
  let := G.finite_edges
  let := Fintype.ofFinite Vertex
  let := Fintype.ofFinite Edge
  have nonempty : Nonempty Vertex := by
    obtain ⟨x, hx⟩ := connected.nonempty
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact ⟨G.anchor i⟩
  refine { preconnected := ?_, nonempty := nonempty }
  intro v w
  by_contra not_reachable
  let A := {i : Vertex ⊕ Edge // G.adjacencyGraph.Reachable v (G.anchor i)}
  let B := {i : Vertex ⊕ Edge // ¬ G.adjacencyGraph.Reachable v (G.anchor i)}
  let first : Set X := ⋃ i : A, G.cell i.val
  let other : Set X := ⋃ i : B, G.cell i.val
  have closed_first : IsClosed first :=
    isClosed_iUnion_of_finite (fun i => (G.compact_cell i.val).isClosed)
  have closed_other : IsClosed other :=
    isClosed_iUnion_of_finite (fun i => (G.compact_cell i.val).isClosed)
  have cover : G.carrier ⊆ first ∪ other := by
    intro x hx
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp hx
    by_cases reachable : G.adjacencyGraph.Reachable v (G.anchor i)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, reachable⟩, member⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, reachable⟩, member⟩)
  have first_nonempty : (G.carrier ∩ first).Nonempty :=
    ⟨G.vertex v, G.mem_carrier_vertex v,
      Set.mem_iUnion.mpr ⟨⟨Sum.inl v, SimpleGraph.Reachable.refl v⟩, rfl⟩⟩
  have other_nonempty : (G.carrier ∩ other).Nonempty :=
    ⟨G.vertex w, G.mem_carrier_vertex w,
      Set.mem_iUnion.mpr ⟨⟨Sum.inl w, not_reachable⟩, rfl⟩⟩
  obtain ⟨x, _, ha, hb⟩ := isPreconnected_closed_iff.mp connected.isPreconnected
    first other closed_first closed_other cover first_nonempty other_nonempty
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  exact j.property (i.property.trans (G.cells_intersection_reachable i.val j.val hi hj))

end FiniteEmbeddedGraph
end Unfoldings
