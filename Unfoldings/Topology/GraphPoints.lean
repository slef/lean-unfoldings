module

public import Unfoldings.Topology.FiniteEmbeddedGraph

/-! Vertex points and closed edge inclusions in the actual graph carrier. -/

@[expose] public section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge X : Type*} [TopologicalSpace X] (G : FiniteEmbeddedGraph Vertex Edge X)

def vertexPoint (v : Vertex) : G.carrier := ⟨G.vertex v, G.mem_carrier_vertex v⟩

def edgeInclusion (e : Edge) : C(unitInterval, G.carrier) :=
  ⟨fun t => ⟨G.edge e t, G.mem_carrier_edge e t⟩,
    (G.edge e).continuous.subtype_mk (G.mem_carrier_edge e)⟩

@[simp] theorem edgeInclusion_zero (e : Edge) : G.edgeInclusion e 0 = G.vertexPoint (G.left e) :=
  Subtype.ext (G.edge_zero e)

@[simp] theorem edgeInclusion_one (e : Edge) : G.edgeInclusion e 1 = G.vertexPoint (G.right e) :=
  Subtype.ext (G.edge_one e)

end Unfoldings.FiniteEmbeddedGraph
