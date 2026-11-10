module

public import Schoenflies.Graph.Cycle
public import Mathlib.Combinatorics.Graph.Maps
public import Unfoldings.Topology.GraphForestMap

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

theorem Connected.mapVertices {f : V → W} (connected : G.Connected) : (G.map f).Connected := by
  obtain ⟨v, member⟩ := connected.1
  refine ⟨⟨f v, Set.mem_image_of_mem f member⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  obtain ⟨edges, walk⟩ := connected.reaches hu hv
  exact ⟨edges, walk.mapVertices f⟩

theorem IsAcyclic.mapVertices {f : V → W} (injective : Function.Injective f)
    (forest : G.IsAcyclic) : (G.map f).IsAcyclic := by
  classical
  by_cases nonempty : Nonempty V
  · let := nonempty
    let inverse := Function.invFun f
    have left_inverse : ∀ v, inverse (f v) = v := Function.leftInverse_invFun injective
    apply forest.of_mapAlong (G := G.map f) (H := G) inverse id _ _ Function.injective_id
    · rintro _ ⟨v, member, rfl⟩
      rw [left_inverse]
      exact member
    · rintro e _ _ ⟨u, v, link, rfl, rfl⟩
      change G.IsLink e (inverse (f u)) (inverse (f v))
      rw [left_inverse, left_inverse]
      exact link
  · intro e _member cycle
    obtain ⟨u, v, _edges, link, _path, _notMem⟩ := cycle
    obtain ⟨u, _v, _link, _first, _last⟩ := link
    exact nonempty ⟨u⟩

theorem Connected.of_mapVertices {f : V → W} (injective : Function.Injective f)
    (connected : (G.map f).Connected) : G.Connected := by
  classical
  obtain ⟨_, v, member, rfl⟩ := connected.1
  let : Nonempty V := ⟨v⟩
  let inverse := Function.invFun f
  have left_inverse : ∀ v, inverse (f v) = v := Function.leftInverse_invFun injective
  refine ⟨⟨v, member⟩, ?_⟩
  intro u hu w hw
  obtain ⟨edges, walk⟩ := connected.reaches
    (Set.mem_image_of_mem f hu) (Set.mem_image_of_mem f hw)
  have mapped : G.IsWalk (inverse (f u)) (edges.map id) (inverse (f w)) :=
    walk.mapAlong (H := G) inverse id (by
      rintro _ ⟨z, hz, rfl⟩
      rw [left_inverse]
      exact hz) (by
      rintro e _ _ ⟨a, b, link, rfl, rfl⟩
      change G.IsLink e (inverse (f a)) (inverse (f b))
      rw [left_inverse, left_inverse]
      exact link)
  rw [left_inverse, left_inverse] at mapped
  exact ⟨edges.map id, mapped⟩

end Graph
