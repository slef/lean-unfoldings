module

public import Unfoldings.Topology.FiniteEmbeddedGraph

/-! Transport finite embedded graphs through continuous injective maps. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (G : FiniteEmbeddedGraph Vertex Edge X) (f : C(X, Y)) (injective : Function.Injective f)

def mapEmbedding : FiniteEmbeddedGraph Vertex Edge Y where
  finite_vertices := G.finite_vertices
  finite_edges := G.finite_edges
  vertex := f ∘ G.vertex
  vertex_injective := injective.comp G.vertex_injective
  left := G.left
  right := G.right
  edge e := f.comp (G.edge e)
  edge_zero e := congrArg f (G.edge_zero e)
  edge_one e := congrArg f (G.edge_one e)
  edge_injective e := fun _ hx _ hy equal => G.edge_injective e hx hy (injective equal)
  edge_avoids_vertices e t positive small v equal :=
    G.edge_avoids_vertices e t positive small v (injective equal)
  disjoint_open_edges e g different := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, equal⟩
    exact Set.disjoint_left.mp (G.disjoint_open_edges e g different)
      ⟨s, hs, rfl⟩ ⟨t, ht, injective equal⟩

theorem mapEmbedding_carrier : (G.mapEmbedding f injective).carrier = f '' G.carrier := by
  ext y
  constructor
  · intro member
    obtain ⟨index, inside⟩ := Set.mem_iUnion.mp member
    cases index with
    | inl vertex =>
      change y ∈ {f (G.vertex vertex)} at inside
      rw [Set.mem_singleton_iff] at inside
      exact ⟨G.vertex vertex, G.mem_carrier_vertex vertex, inside.symm⟩
    | inr edge =>
      obtain ⟨t, rfl⟩ := inside
      exact ⟨G.edge edge t, G.mem_carrier_edge edge t, rfl⟩
  · rintro ⟨x, member, rfl⟩
    obtain ⟨index, inside⟩ := Set.mem_iUnion.mp member
    cases index with
    | inl vertex =>
      change x ∈ {G.vertex vertex} at inside
      rw [Set.mem_singleton_iff] at inside
      rw [inside]
      exact (G.mapEmbedding f injective).mem_carrier_vertex vertex
    | inr edge =>
      obtain ⟨t, rfl⟩ := inside
      exact (G.mapEmbedding f injective).mem_carrier_edge edge t

end Unfoldings.FiniteEmbeddedGraph
