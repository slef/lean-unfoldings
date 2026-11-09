module

public import Unfoldings.Source.CutSegments
public import Unfoldings.Source.CutConnected
public import Unfoldings.Geometry.SegmentGraph

/-!
# The source cut locus has a constructed finite connected embedded graph

Subdivide the proved straight network at all crossings and overlap endpoints.
The resulting actual graph has precisely the spatial cut locus as its carrier,
and every straight edge lies in an original triangle. Its graph connectedness
is derived from the proved topological connectedness of that cut locus.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_finite_source_cut_graph :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
        G.IsStraight ∧ G.graph.Simple ∧ G.adjacencyGraph.Connected ∧
          G.carrier = F.toSpace Set.univ '' sourceCutLocus source ∧
          ∀ e : Edge, ∃ f : Face, Set.range (G.edge e) ⊆
            (F.place f) '' (C.triangle f).carrier := by
  let := P.metricSpace
  intro source R
  obtain ⟨segments, finite, cover, faces⟩ := P.exists_finite_source_cut_segments R
  obtain ⟨Vertex, Edge, G, straight, carrier, refines⟩ :=
    exists_finite_embedded_straight_segment_graph segments finite
  have exact_carrier : G.carrier = F.toSpace Set.univ '' sourceCutLocus source :=
    carrier.trans cover.symm
  have connected : IsConnected G.carrier := by
    rw [exact_carrier]
    exact (P.sourceCutLocus_isConnected R).image (F.toSpace Set.univ)
      (F.toSpace_lipschitz Set.univ).continuous.continuousOn
  refine ⟨Vertex, Edge, G, straight, straight.graph_simple, G.connected_of_isConnected connected,
    exact_carrier, ?_⟩
  intro e
  obtain ⟨p, hp, included⟩ := refines e
  obtain ⟨f, in_face⟩ := faces p hp
  exact ⟨f, included.trans in_face⟩

end Unfoldings.SpatialFolding.ConvexBoundary
