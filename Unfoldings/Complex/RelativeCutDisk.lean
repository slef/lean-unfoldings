module

public import Unfoldings.Complex.RelativeBoundaryConnectivity
public import Unfoldings.Complex.DiskCuts

/-!
# Construct disk cuts from rooted cut forests

The original surface is an actual disk. The only graph edges are its newly
removed interior seams. Acyclicity and exactly one original-boundary root per
component construct the homeomorphism of the further cut to a closed disk.
Existing boundary edges and empty cuts are included by the same proof.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

include F inclusion in
theorem exists_cutDisk_of_rootedForest
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (rooted : (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large)) :
    Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  have tree := (C.relativeCutRootExtension_tree_iff small large).mpr rooted
  exact F.exists_cutDisk_of_boundaryGraph_connected inclusion original
    (C.boundaryGraph_connected_of_relativeCutTree inclusion tree.isAcyclic
      (F.boundaryGraph_connected_of_disk large original) tree.connected)

def cutDiskHomeomorphOfRootedForest
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (rooted : (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large)) :
    C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  Classical.choice (F.exists_cutDisk_of_rootedForest inclusion original rooted)

theorem cutDiskHomeomorphOfRootedForest_boundary
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (rooted : (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large))
    (x : C.Realization small) :
    x ∈ C.bankBoundary small ↔
      ‖(F.cutDiskHomeomorphOfRootedForest inclusion original rooted x).val‖ = 1 :=
  F.bankBoundary_iff_disk_norm_eq_one small
    (F.cutDiskHomeomorphOfRootedForest inclusion original rooted) x

end Unfoldings.SpatialFolding
