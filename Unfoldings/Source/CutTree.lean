module

public import Unfoldings.Source.CutContractible
public import Unfoldings.Source.Unfolding
public import Unfoldings.Topology.GraphAcyclic

/-!
# The actual source cut locus is a finite embedded tree

The source cut locus is an exact finite straight segment network. Its carrier
is contractible because it is a retract of the punctured convex boundary.
The generic topological graph theorem therefore proves acyclicity. No Euler
formula, planar separation hypothesis, or assumed tree property is needed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_source_cut_tree :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
        G.IsStraight ∧ G.graph.Simple ∧ G.adjacencyGraph.IsTree ∧
          G.carrier = F.toSpace Set.univ '' sourceCutLocus source ∧
          ∀ e : Edge, ∃ f : Face, Set.range (G.edge e) ⊆
            (F.place f) '' (C.triangle f).carrier := by
  let := P.metricSpace
  intro source R
  obtain ⟨Vertex, Edge, G, straight, simple, _, contractible, carrier, faces⟩ :=
    P.exists_contractible_source_cut_graph R
  let := contractible
  exact ⟨Vertex, Edge, G, straight, simple, G.adjacencyGraph_tree_of_contractible, carrier, faces⟩

theorem exists_source_cut_tree_of_nonextreme :
    letI := P.metricSpace
    ∀ (source : C.Realization Set.univ),
      F.toSpace Set.univ source ∉ F.vertexHull.extremePoints ℝ →
      ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
        G.IsStraight ∧ G.graph.Simple ∧ G.adjacencyGraph.IsTree ∧
          G.carrier = F.toSpace Set.univ '' sourceCutLocus source ∧
          ∀ e : Edge, ∃ f : Face, Set.range (G.edge e) ⊆
            (F.place f) '' (C.triangle f).carrier := by
  let := P.metricSpace
  intro source nonextreme
  exact P.exists_source_cut_tree (P.sourceUnfoldingOfNonextreme source nonextreme).frame

end Unfoldings.SpatialFolding.ConvexBoundary
