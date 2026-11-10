module

public import Unfoldings.Complex.IntrinsicBoundary
public import Unfoldings.Topology.DiskSphereQuotient

/-!
# Restore cuts and collapse the original disk boundary

Original banks persist when cuts are added. Consequently every preimage of the
old boundary is on the new bank boundary. Restoring cuts, presenting the old
surface as a disk, and collapsing its boundary therefore form one actual
boundary quotient from the new cut surface to a sphere.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem bankBoundary_preimage_forgetCuts {small large : Set C.Seam} (inclusion : small ⊆ large) :
    C.forgetCuts inclusion ⁻¹' C.bankBoundary large ⊆ C.bankBoundary small := by
  intro x member
  obtain ⟨bank, y, equal⟩ := Set.mem_iUnion.mp member
  let original : C.BoundaryBank small :=
    ⟨bank.val, C.isBoundaryEdge_antitone inclusion bank.property⟩
  let copy := C.bankMap small original y
  have on_boundary : copy ∈ C.bankBoundary small := C.bankMap_mem_bankBoundary small original y
  have image : C.forgetCuts inclusion copy = C.forgetCuts inclusion x := by
    change C.forgetCuts inclusion
      (C.faceMap small bank.val.face ((C.triangle bank.val.face).edgeMap bank.val.edge y)) = _
    rw [C.forgetCuts_faceMap]
    exact equal
  rcases C.forgetCuts_fiber_eq_or_boundary inclusion copy x image with same | both
  · exact same ▸ on_boundary
  · exact both.2

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

def cutDiskBoundarySphereQuotient {small large : Set C.Seam} (inclusion : small ⊆ large)
    (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    BoundaryQuotient (C.Realization small) (Metric.sphere (0 : Space) 1) :=
  (closedDiskSphereQuotient.precomp disk).comp (C.forgetCutsBoundaryQuotient inclusion) (by
    intro x boundary
    apply C.bankBoundary_preimage_forgetCuts inclusion
    exact (F.bankBoundary_iff_disk_norm_eq_one large disk _).mpr boundary)

@[simp] theorem cutDiskBoundarySphereQuotient_boundary {small large : Set C.Seam}
    (inclusion : small ⊆ large) (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    (F.cutDiskBoundarySphereQuotient inclusion disk).boundary = C.bankBoundary small := rfl

/-- If the further cut is a disk, its boundary image after collapsing the old
boundary is contractible. In particular, cycles and paths joining distinct
old boundary roots are topologically obstructed. -/
theorem cutDiskBoundarySphereImage_contractible {small large : Set C.Seam}
    (inclusion : small ⊆ large)
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (cut : C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) :
    ContractibleSpace (F.cutDiskBoundarySphereQuotient inclusion original).boundaryImage := by
  let Q := (F.cutDiskBoundarySphereQuotient inclusion original).precomp cut.symm
  have boundary : Q.boundary = closedBallBoundary := by
    ext x
    change cut.symm x ∈ C.bankBoundary small ↔ ‖x.val‖ = 1
    simpa only [cut.apply_symm_apply] using
      F.bankBoundary_iff_disk_norm_eq_one small cut (cut.symm x)
  have result := Q.ball_boundaryImage_contractible_of_sphere (Homeomorph.refl _) boundary
  have image : Q.boundaryImage =
      (F.cutDiskBoundarySphereQuotient inclusion original).boundaryImage := by
    exact (F.cutDiskBoundarySphereQuotient inclusion original).precomp_boundaryImage cut.symm
  rwa [image] at result

end Unfoldings.SpatialFolding
