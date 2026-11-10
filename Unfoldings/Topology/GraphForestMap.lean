module

public import Schoenflies.Graph.Cycle

/-!
# A cycle mapped to a forest must repeat its distinguished edge

Vertex and edge maps preserve actual links. Mapping the alternate path of a
cycle to a forest forces another edge to have the same image as the omitted
edge: otherwise the image edge itself would lie on a cycle. This supplies the
bridge argument for paired banks in tree cuts.
-/

@[expose] public section

namespace Graph

variable {V W E F : Type*} {G : Graph V E} {H : Graph W F}
  (vertices : V → W) (edges : E → F)
  (members : ∀ v ∈ G.vertexSet, vertices v ∈ H.vertexSet)
  (links : ∀ {e u v}, G.IsLink e u v → H.IsLink (edges e) (vertices u) (vertices v))

include members links in
theorem IsWalk.mapAlong {u v : V} {walk : List E} (actual : G.IsWalk u walk v) :
    H.IsWalk (vertices u) (walk.map edges) (vertices v) := by
  induction actual with
  | nil member => exact .nil (members _ member)
  | cons link _ ih => exact .cons (links link) ih

include vertices members links in
theorem IsCycleThrough.exists_other_edge_of_map_to_forest (forest : H.IsAcyclic)
    {e : E} {u v : V} {detour : List E} (cycle : G.IsCycleThrough e u v detour) :
    ∃ f ∈ detour, f ≠ e ∧ edges f = edges e := by
  by_contra none
  have omitted : edges e ∉ detour.map edges := by
    intro member
    obtain ⟨f, hf, same⟩ := List.mem_map.mp member
    exact none ⟨f, hf, (fun equal => cycle.notMem (equal ▸ hf)), same⟩
  have walk := cycle.isPath.isWalk.mapAlong vertices edges members @links
  have reaches : (H.deleteEdges {edges e}).Reaches (vertices u) (vertices v) := by
    apply walk.reaches_deleteEdges
    intro f hf same
    have equal : f = edges e := same
    exact omitted (equal ▸ hf)
  have closed := LiesOnCycle.of_deleteEdges_reaches (links cycle.isLink) reaches
  exact forest.not_liesOnCycle (edges e) closed

end Graph
