module

public import Unfoldings.Polyhedron.CutJordan
public import Unfoldings.Topology.SphereSubsetChart
public import Unfoldings.Topology.DiskFromBoundary

/-!
# A primal cut tree on a convex sphere produces an actual cut disk

The exact bank boundary is a single Jordan curve in the constructed planar
embedding. Its complement has an open planar model inherited from the original
sphere. The intrinsic half-plane atlas identifies the embedded frontier, so
compact Jordan classification constructs the disk homeomorphism. Overlap of
any separate planar development plays no role.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_cutComplementOpenEmbedding (retain : Set C.Seam)
    (cut : (C.bankBoundary retain).Nonempty) :
    ∃ i : ↥((C.bankBoundary retain)ᶜ) → Plane, Topology.IsOpenEmbedding i := by
  let inclusion : retain ⊆ (Set.univ : Set C.Seam) := Set.subset_univ _
  let Q := C.forgetCutsBoundaryQuotient inclusion
  obtain ⟨p, boundary⟩ := cut
  have image_nonempty : Q.boundaryImage.Nonempty := ⟨Q.projection p, p, boundary, rfl⟩
  let : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  obtain ⟨i, embedding⟩ := exists_openEmbedding_sphere_compl 2 P.sphereHomeomorph
    (Q.isClosed_boundaryImage (C.isClosed_bankBoundary retain)) image_nonempty
  let h := Q.complementHomeomorph (C.isClosed_bankBoundary retain)
  exact ⟨i ∘ h, embedding.comp h.isOpenEmbedding⟩

theorem exists_cutDisk_of_tree (retain : Set C.Seam)
    (forest : (C.cutSeamGraph retain).IsAcyclic) (connected : (C.cutSeamGraph retain).Connected) :
    Nonempty (C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  obtain ⟨f, embedded, jordan⟩ := P.exists_Jordan_bankBoundary_of_cutTree retain forest connected
  have cut : (C.bankBoundary retain).Nonempty := by
    obtain ⟨y, x, hx, _equal⟩ := jordan.nonempty
    exact ⟨x, hx⟩
  obtain ⟨i, embedding⟩ := P.exists_cutComplementOpenEmbedding retain cut
  exact exists_diskHomeomorph_of_Jordan_boundary (F.exists_bankBoundaryChart retain)
    i embedding f embedded.injective jordan

/-- Choose the disk presentation after deriving it from the actual primal cut tree. -/
def cutDiskHomeomorphOfTree (retain : Set C.Seam)
    (forest : (C.cutSeamGraph retain).IsAcyclic) (connected : (C.cutSeamGraph retain).Connected) :
    C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  Classical.choice (P.exists_cutDisk_of_tree retain forest connected)

theorem cutDiskHomeomorphOfTree_boundary (retain : Set C.Seam)
    (forest : (C.cutSeamGraph retain).IsAcyclic) (connected : (C.cutSeamGraph retain).Connected)
    (x : C.Realization retain) :
    x ∈ C.bankBoundary retain ↔ ‖(P.cutDiskHomeomorphOfTree retain forest connected x).val‖ = 1 :=
  F.bankBoundary_iff_disk_norm_eq_one retain (P.cutDiskHomeomorphOfTree retain forest connected) x

end Unfoldings.SpatialFolding.ConvexBoundary
