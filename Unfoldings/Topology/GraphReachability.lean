module

public import Schoenflies.Graph.Walk
public import Unfoldings.Topology.FiniteEmbeddedGraph

/-! Every vertex visited by an actual multigraph walk is reachable from its source. -/

@[expose] public section

namespace Graph

variable {V E : Type*} {G : Graph V E}

theorem IsWalk.reaches_mem_walkVertices {u v x : V} {edges : List E}
    (walk : G.IsWalk u edges v) (visited : x ∈ G.walkVertices u edges) : G.Reaches u x := by
  induction walk generalizing x with
  | @nil w member =>
    have same : x = w := by simpa using visited
    subst x
    exact Reaches.refl member
  | cons link _ ih =>
    rcases mem_walkVertices_cons link visited with rfl | rest
    · exact Reaches.refl link.left_mem
    · exact (Reaches.of_isLink link).trans (ih rest)

theorem IsWalk.eq_of_link_invariant {K : Type*} (color : V → K)
    (compatible : ∀ {e u v}, G.IsLink e u v → color u = color v)
    {u v : V} {edges : List E} (walk : G.IsWalk u edges v) : color u = color v := by
  induction walk with
  | nil _ => rfl
  | cons link _ ih => exact (compatible link).trans ih

theorem IsWalk.propagate (P : V → Prop)
    (step : ∀ {e u v}, G.IsLink e u v → P u → P v)
    {u v : V} {edges : List E} (walk : G.IsWalk u edges v) : P u → P v := by
  induction walk with
  | nil _ => exact id
  | cons link _ ih => exact fun initial => ih (step link initial)

end Graph

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [TopologicalSpace X] (G : FiniteEmbeddedGraph V E X)

theorem graph_reaches_iff_adjacency {u v : V} :
    G.graph.Reaches u v ↔ G.adjacencyGraph.Reachable u v := by
  constructor
  · rintro ⟨edges, walk⟩
    induction walk with
    | nil _ => exact SimpleGraph.Reachable.rfl
    | @cons u w v edge edges link _ ih =>
      have step : G.adjacencyGraph.Reachable u w := by
        rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact G.endpoints_reachable edge
        · exact (G.endpoints_reachable edge).symm
      exact step.trans ih
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact Graph.Reaches.refl (Set.mem_univ _)
    | cons adjacent _ ih =>
      obtain ⟨_different, edge, link⟩ := adjacent
      exact (Graph.Reaches.of_isLink (show G.graph.IsLink edge _ _ from link)).trans ih

end Unfoldings.FiniteEmbeddedGraph
