module

public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Topology.BallBoundaryQuotient

/-!
# Necessary topology of edge cuts producing one disk

A boundary-preserving disk homeomorphism for the actual cut realization makes
its bank image the boundary image of a standard disk quotient. Its complement
is an open disk. When restoring the seams produces a sphere, every finite
embedded graph with exactly that bank image as carrier must be simple and a
tree. These statements use the actual canonical seam-restoration map.

The hypotheses include the disk homeomorphism and its identification of the
unpaired banks with the disk boundary. Constructing such a homeomorphism from
an arbitrary embedded cut tree remains the converse problem.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (disk : C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1)

def cutDiskBoundaryQuotient :
    BoundaryQuotient (Metric.closedBall (0 : Plane) 1) (C.Realization large) :=
  (C.forgetCutsBoundaryQuotient inclusion).precomp disk.symm

theorem cutDiskBoundaryQuotient_boundaryImage :
    (C.cutDiskBoundaryQuotient inclusion disk).boundaryImage =
      C.forgetCuts inclusion '' C.bankBoundary small :=
  (C.forgetCutsBoundaryQuotient inclusion).precomp_boundaryImage disk.symm

theorem cutDiskBoundaryQuotient_boundary
    (boundary : ∀ x, x ∈ C.bankBoundary small ↔ ‖(disk x).val‖ = 1) :
    (C.cutDiskBoundaryQuotient inclusion disk).boundary = closedBallBoundary := by
  ext z
  change disk.symm z ∈ C.bankBoundary small ↔ ‖z.val‖ = 1
  simpa only [disk.apply_symm_apply] using boundary (disk.symm z)

def cutComplementDiskHomeomorph
    (boundary : ∀ x, x ∈ C.bankBoundary small ↔ ‖(disk x).val‖ = 1) :
    Metric.ball (0 : Plane) 1 ≃ₜ
      ↥((C.forgetCuts inclusion '' C.bankBoundary small)ᶜ) :=
  ((C.cutDiskBoundaryQuotient inclusion disk).ballComplementHomeomorph
    (C.cutDiskBoundaryQuotient_boundary inclusion disk boundary)).trans
      (Homeomorph.setCongr
        (congrArg Set.compl (C.cutDiskBoundaryQuotient_boundaryImage inclusion disk)))

@[simp] theorem cutComplementDiskHomeomorph_apply
    (boundary : ∀ x, x ∈ C.bankBoundary small ↔ ‖(disk x).val‖ = 1)
    (x : Metric.ball (0 : Plane) 1) :
    (C.cutComplementDiskHomeomorph inclusion disk boundary x).val =
      C.forgetCuts inclusion (disk.symm ⟨x.val, Metric.ball_subset_closedBall x.property⟩) := rfl

theorem bankBoundaryImage_tree_of_cutDisk
    (sphere : C.Realization large ≃ₜ Metric.sphere (0 : Space) 1)
    (boundary : ∀ x, x ∈ C.bankBoundary small ↔ ‖(disk x).val‖ = 1)
    {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge (C.Realization large))
    (carrier : G.carrier = C.forgetCuts inclusion '' C.bankBoundary small) :
    G.graph.Simple ∧ G.adjacencyGraph.IsTree := by
  apply (C.cutDiskBoundaryQuotient inclusion disk).ball_boundary_graph_tree_of_sphere sphere
    (C.cutDiskBoundaryQuotient_boundary inclusion disk boundary) G
  exact carrier.trans (C.cutDiskBoundaryQuotient_boundaryImage inclusion disk).symm

end Unfoldings.TriangleComplex
