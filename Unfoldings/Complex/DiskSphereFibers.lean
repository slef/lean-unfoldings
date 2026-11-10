module

public import Unfoldings.Complex.DiskBoundaryQuotient

/-! Exact fibers of the sphere quotient of the original disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem closedDiskSphereQuotient_fibers (x y : Metric.closedBall (0 : Plane) 1) :
    closedDiskSphereQuotient.projection x = closedDiskSphereQuotient.projection y ↔
      x = y ∨ (x ∈ closedBallBoundary ∧ y ∈ closedBallBoundary) := by
  change diskBoundarySphereHomeomorph (collapseBoundary closedBallBoundary x) =
    diskBoundarySphereHomeomorph (collapseBoundary closedBallBoundary y) ↔ _
  rw [diskBoundarySphereHomeomorph.injective.eq_iff, collapseBoundary_fibers]

namespace SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

def originalDiskSphereProjection {retain : Set C.Seam}
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) :
    C(C.Realization retain, Metric.sphere (0 : Space) 1) :=
  closedDiskSphereQuotient.projection.comp ⟨disk, disk.continuous⟩

include F in
theorem originalDiskSphereProjection_fibers {retain : Set C.Seam}
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (x y : C.Realization retain) :
    originalDiskSphereProjection disk x = originalDiskSphereProjection disk y ↔
      x = y ∨ (x ∈ C.bankBoundary retain ∧ y ∈ C.bankBoundary retain) := by
  change closedDiskSphereQuotient.projection (disk x) =
    closedDiskSphereQuotient.projection (disk y) ↔ _
  rw [closedDiskSphereQuotient_fibers, disk.injective.eq_iff]
  change x = y ∨ (‖(disk x).val‖ = 1 ∧ ‖(disk y).val‖ = 1) ↔ _
  rw [← F.bankBoundary_iff_disk_norm_eq_one retain disk x,
    ← F.bankBoundary_iff_disk_norm_eq_one retain disk y]

end SpatialFolding
end Unfoldings
