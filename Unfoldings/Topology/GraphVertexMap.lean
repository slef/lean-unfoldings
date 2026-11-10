module

public import Schoenflies.Graph.Cycle
public import Mathlib.Combinatorics.Graph.Maps

/-! Injective relabeling of vertices preserves actual multigraph paths and cycles. -/

@[expose] public section

namespace Graph

variable {V W E : Type*} {G : Graph V E} (f : V → W)

theorem walkVertices_map (u : V) (edges : List E) :
    (G.map f).walkVertices (f u) edges = f '' G.walkVertices u edges := by
  ext y
  rw [mem_walkVertices_iff]
  constructor
  · rintro (same | ⟨edge, member, incidence⟩)
    · exact ⟨u, mem_walkVertices_self, same.symm⟩
    · obtain ⟨v, incident, equal⟩ := (map_inc f).mp incidence
      exact ⟨v, mem_walkVertices_of_mem_covered ⟨edge, member, incident⟩, equal.symm⟩
  · rintro ⟨v, member, rfl⟩
    rcases mem_walkVertices_iff.mp member with rfl | ⟨edge, member, incidence⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨edge, member, incidence.map f⟩

theorem IsWalk.mapVertices {u v : V} {edges : List E} (walk : G.IsWalk u edges v) :
    (G.map f).IsWalk (f u) edges (f v) := by
  induction walk with
  | nil member => exact .nil (Set.mem_image_of_mem f member)
  | cons link _ ih => exact .cons (link.map f) ih

theorem IsPath.mapVertices (injective : Function.Injective f)
    {u v : V} {edges : List E} (path : G.IsPath u edges v) :
    (G.map f).IsPath (f u) edges (f v) := by
  induction path with
  | nil member => exact .nil (Set.mem_image_of_mem f member)
  | cons link _ fresh ih =>
    apply IsPath.cons (link.map f) ih
    rw [walkVertices_map]
    rintro ⟨x, member, same⟩
    exact fresh (injective same ▸ member)

theorem IsCycleThrough.mapVertices (injective : Function.Injective f)
    {u v : V} {edge : E} {detour : List E} (cycle : G.IsCycleThrough edge u v detour) :
    (G.map f).IsCycleThrough edge (f u) (f v) detour :=
  ⟨cycle.isLink.map f, cycle.isPath.mapVertices f injective, cycle.notMem⟩

end Graph
