module

public import Unfoldings.Complex.CutDisk
public import Unfoldings.Complex.CutGraph
public import Unfoldings.Polyhedron.Convex

/-!
# Edge cuts producing a boundary-preserving disk have a tree image

For a convex boundary, construct the actual finite embedded straight graph of
all cut-bank images. A disk presentation identifying its boundary with the
unpaired banks forces this graph to be a tree. The graph is constructed from
the actual spatial bank segments, rather than supplied as an extra hypothesis.
The tree-to-disk converse and intrinsic manifold boundary identification are
separate construction tasks.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P in
theorem exists_cut_tree_of_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (boundary : ∀ x, x ∈ C.bankBoundary retain ↔ ‖(disk x).val‖ = 1) :
    ∃ (Vertex Edge : Type) (G : FiniteEmbeddedGraph Vertex Edge Space),
      G.IsStraight ∧ G.graph.Simple ∧ G.adjacencyGraph.IsTree ∧
        G.carrier = F.toSpace retain '' C.bankBoundary retain ∧
        ∀ e : Edge, ∃ bank : C.BoundaryBank retain,
          Set.range (G.edge e) ⊆ F.toSpace retain '' Set.range (C.bankMap retain bank) := by
  let inclusion : retain ⊆ Set.univ := Set.subset_univ _
  let Q := C.cutDiskBoundaryQuotient inclusion disk
  have boundary_eq := C.cutDiskBoundaryQuotient_boundary inclusion disk boundary
  let := Q.ball_boundaryImage_contractible_of_sphere P.sphereHomeomorph boundary_eq
  have embedding : Topology.IsEmbedding (F.toSpace Set.univ) :=
    ((F.toSpace_lipschitz Set.univ).continuous.isClosedEmbedding P.embedded).isEmbedding
  have image : F.toSpace Set.univ '' Q.boundaryImage =
      F.toSpace retain '' C.bankBoundary retain := by
    rw [C.cutDiskBoundaryQuotient_boundaryImage, ← Set.image_comp]
    congr 1
    funext x
    exact F.toSpace_forgetCuts inclusion x
  have contractible : ContractibleSpace (F.toSpace retain '' C.bankBoundary retain) := by
    rw [← image]
    exact (embedding.homeomorphImage Q.boundaryImage).symm.contractibleSpace
  obtain ⟨Vertex, Edge, G, straight, simple, carrier, parents⟩ :=
    F.exists_bank_boundary_graph retain
  have graph_contractible : ContractibleSpace G.carrier := by
    rwa [carrier]
  let := graph_contractible
  exact ⟨Vertex, Edge, G, straight, simple, G.adjacencyGraph_tree_of_contractible, carrier, parents⟩

end Unfoldings.SpatialFolding.ConvexBoundary
