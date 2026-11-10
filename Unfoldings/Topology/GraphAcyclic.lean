module

public import Unfoldings.Topology.GraphPotential
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic.Linarith
public import Unfoldings.Topology.GraphReachability
public import Schoenflies.Graph.Cycle

/-!
# Contractible finite embedded graphs are trees

A real potential that changes along one selected edge and stays constant along
all other edges makes the selected edge a bridge. Contractibility supplies
these potentials through covering-space lifting. The argument also excludes
loops and parallel edges in the original multigraph.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X : Type*} [TopologicalSpace X] [T2Space X]
  (G : FiniteEmbeddedGraph Vertex Edge X) [ContractibleSpace G.carrier]

theorem graph_simple_of_contractible : G.graph.Simple := by
  rw [Graph.simple_iff, Graph.loopless_iff]
  constructor
  · intro e v loop
    obtain ⟨value, difference, _⟩ := G.exists_edge_potential e
    rcases loop with ⟨left, right⟩ | ⟨right, left⟩
    all_goals rw [← left, ← right] at difference
    all_goals linarith
  · intro e f x y first second
    by_contra different
    obtain ⟨value, difference, others⟩ := G.exists_edge_potential e
    have same : value x = value y := by
      have equal := others f (Ne.symm different)
      rcases second with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact equal
      · exact equal.symm
    rcases first with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals linarith

theorem adjacencyGraph_acyclic_of_contractible : G.adjacencyGraph.IsAcyclic := by
  classical
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y adjacent
  obtain ⟨_, e, link⟩ := adjacent
  obtain ⟨value, difference, others⟩ := G.exists_edge_potential e
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨walk⟩
  have preserves {u v : Vertex}
      (step : (G.adjacencyGraph.deleteEdges {s(x, y)}).Adj u v) : value u = value v := by
    obtain ⟨⟨_, f, other_link⟩, remains⟩ := SimpleGraph.deleteEdges_adj.mp step
    have different : f ≠ e := by
      intro equal
      subst f
      have first : G.graph.IsLink e x y := link
      have second : G.graph.IsLink e u v := other_link
      have same : s(x, y) = s(u, v) := first.isLink_iff_sym2_eq.mp second
      exact remains (Set.mem_singleton_iff.mpr same.symm)
    have equal := others f different
    rcases other_link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact equal
    · exact equal.symm
  have walk_preserves {u v : Vertex}
      (w : (G.adjacencyGraph.deleteEdges {s(x, y)}).Walk u v) : value u = value v := by
    induction w with
    | nil => rfl
    | cons adj tail ih => exact (preserves adj).trans ih
  have same := walk_preserves walk
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals linarith

/-- Acyclicity in the multigraph itself, retaining loops and parallel edges. -/
theorem graph_acyclic_of_contractible : G.graph.IsAcyclic := by
  intro e _member cycle
  obtain ⟨u, v, detour, link, path, omitted⟩ := cycle
  obtain ⟨value, difference, others⟩ := G.exists_edge_potential e
  have step {f : Edge} {a b : Vertex}
      (actual : (G.graph.deleteEdges {e}).IsLink f a b) : value a = value b := by
    obtain ⟨link, different⟩ := actual
    have same := others f (fun equal => different equal)
    rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact same
    · exact same.symm
  have avoiding := path.isWalk.deleteEdges (F := {e}) (fun f member equal =>
    omitted ((show f = e from equal) ▸ member))
  have same := avoiding.eq_of_link_invariant value @step
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals linarith

theorem adjacencyGraph_tree_of_contractible : G.adjacencyGraph.IsTree := by
  have connected : IsConnected G.carrier := isConnected_iff_connectedSpace.mpr inferInstance
  exact ⟨G.connected_of_isConnected connected, G.adjacencyGraph_acyclic_of_contractible⟩

end Unfoldings.FiniteEmbeddedGraph
