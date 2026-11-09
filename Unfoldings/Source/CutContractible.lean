module

public import Unfoldings.Source.BoundaryQuotient
public import Unfoldings.Source.CutRetraction
public import Unfoldings.Source.CutGraph
public import Unfoldings.Topology.PuncturedSphere

/-!
# The source cut locus and its constructed graph carrier are contractible

The original convex boundary is a sphere. Removing the source gives a
contractible space by stereographic projection. The constructed continuous
cut-locus retraction therefore proves contractibility of the actual cut locus.
The embedded graph inherits this property through the spatial embedding.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
theorem sourcePunctured_contractible :
    letI := P.metricSpace
    ∀ source : C.Realization Set.univ,
      ContractibleSpace ↥(({source} : Set (C.Realization Set.univ))ᶜ) := by
  let := P.metricSpace
  intro source
  let H := P.sphereHomeomorph
  let punctured : ↥(({source} : Set (C.Realization Set.univ))ᶜ) ≃ₜ
      ↥(({H source} : Set (Metric.sphere (0 : Space) 1))ᶜ) := H.subtype (by
    intro x
    change x ≠ source ↔ H x ≠ H source
    exact not_congr H.injective.eq_iff.symm)
  let := contractible_punctured_unit_sphere (H source)
  exact punctured.contractibleSpace

theorem sourceCutLocus_contractible :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ContractibleSpace (sourceCutLocus source) := by
  let := P.metricSpace
  intro source R
  have contractible := (P.sourceDiskBoundaryQuotient R).ball_boundaryImage_contractible_of_sphere
    P.sphereHomeomorph (P.sourceDiskBoundaryQuotient_boundary R)
  rwa [P.sourceDiskBoundaryQuotient_boundaryImage R] at contractible

theorem sourceCutLocus_spatial_contractible :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ContractibleSpace (F.toSpace Set.univ '' sourceCutLocus source) := by
  let := P.metricSpace
  intro source R
  let := P.sourceCutLocus_contractible R
  have embedded : Topology.IsEmbedding (F.toSpace Set.univ) :=
    ((F.toSpace_lipschitz Set.univ).continuous.isClosedEmbedding P.embedded).isEmbedding
  exact (embedded.homeomorphImage (sourceCutLocus source)).symm.contractibleSpace

theorem exists_contractible_source_cut_graph :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
        G.IsStraight ∧ G.graph.Simple ∧ G.adjacencyGraph.Connected ∧
          ContractibleSpace G.carrier ∧
          G.carrier = F.toSpace Set.univ '' sourceCutLocus source ∧
          ∀ e : Edge, ∃ f : Face, Set.range (G.edge e) ⊆
            (F.place f) '' (C.triangle f).carrier := by
  let := P.metricSpace
  intro source R
  obtain ⟨Vertex, Edge, G, straight, simple, connected, carrier, faces⟩ :=
    P.exists_finite_source_cut_graph R
  refine ⟨Vertex, Edge, G, straight, simple, connected, ?_, carrier, faces⟩
  rw [carrier]
  exact P.sourceCutLocus_spatial_contractible R

end Unfoldings.SpatialFolding.ConvexBoundary
