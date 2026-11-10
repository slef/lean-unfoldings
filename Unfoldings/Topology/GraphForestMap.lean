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

include vertices members links in
theorem IsAcyclic.of_mapAlong (forest : H.IsAcyclic) (injective : Function.Injective edges) :
    G.IsAcyclic := by
  intro e _member cycle
  obtain ⟨u, v, detour, actual⟩ := cycle
  obtain ⟨_f, _member, different, equal⟩ :=
    actual.exists_other_edge_of_map_to_forest vertices edges members @links forest
  exact different (injective equal)

include vertices members links in
/-- A map into a forest with distinct edge names cannot identify the ends of
any nontrivial path. Vertex injectivity is a conclusion on each component. -/
theorem IsPath.eq_of_map_eq (forest : H.IsAcyclic) (injective : Function.Injective edges)
    {u v : V} {walk : List E} (path : G.IsPath u walk v)
    (equal : vertices u = vertices v) : u = v := by
  cases path with
  | nil _ => rfl
  | @cons u w v e tail link rest fresh =>
    have omitted : edges e ∉ tail.map edges := by
      rintro member
      obtain ⟨f, member, same⟩ := List.mem_map.mp member
      have e_member : e ∈ tail := injective same ▸ member
      exact fresh (mem_walkVertices_of_mem_covered ⟨e, e_member, link.inc_left⟩)
    have alt : (H.deleteEdges {edges e}).Reaches (vertices w) (vertices u) := by
      rw [equal]
      apply (rest.isWalk.mapAlong vertices edges members @links).reaches_deleteEdges
      intro f member same
      have equal : f = edges e := same
      exact omitted (equal ▸ member)
    exact ((forest.isBridge (links link).edge_mem).not_reaches (links link).symm alt).elim

include vertices members links in
theorem Reaches.eq_of_map_eq (forest : H.IsAcyclic) (injective : Function.Injective edges)
    {u v : V} (reach : G.Reaches u v) (equal : vertices u = vertices v) : u = v := by
  obtain ⟨walk, path⟩ := reach.exists_isPath
  exact path.eq_of_map_eq vertices edges members @links forest injective equal

end Graph
