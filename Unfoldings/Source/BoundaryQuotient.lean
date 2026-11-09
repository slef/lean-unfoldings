module

public import Unfoldings.Source.ProjectionFibers
public import Unfoldings.Topology.BallBoundaryQuotient

/-!
# The source disk as a boundary-only quotient presentation

The actual source projection identifies points only on the developed boundary.
Transporting its domain by the constructed disk homeomorphism gives a standard
closed-ball presentation. Its boundary image is exactly the actual cut locus.
This connects the general spherical boundary-quotient theorem to unfoldings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceBoundaryQuotient :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      BoundaryQuotient R.domain (C.Realization Set.univ) := by
  let := P.metricSpace
  intro source R
  let := isCompact_iff_compactSpace.mp R.compact_domain
  exact
    { projection := ⟨R.projection (P.sourcePathCoordinate_injective R),
        R.continuous_projection (P.sourcePathCoordinate_injective R)⟩
      quotient := Topology.IsQuotientMap.of_surjective_continuous
        (P.sourceProjection_surjective R)
        (R.continuous_projection (P.sourcePathCoordinate_injective R))
      boundary := {z : R.domain | z.val ∈ frontier R.domain}
      fibers := fun z w equal => P.sourceProjection_fiber_eq_or_boundary R z w equal }

theorem sourceBoundaryQuotient_boundaryImage :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      (P.sourceBoundaryQuotient R).boundaryImage = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  exact P.sourceDomain_boundary_projection_cutLocus R

def sourceDiskBoundaryQuotient :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      BoundaryQuotient (Metric.closedBall (0 : Plane) 1) (C.Realization Set.univ) := by
  let := P.metricSpace
  intro source R
  exact (P.sourceBoundaryQuotient R).precomp (P.sourceDomainDiskHomeomorph R).symm

theorem sourceDiskBoundaryQuotient_boundaryImage :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      (P.sourceDiskBoundaryQuotient R).boundaryImage = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  exact ((P.sourceBoundaryQuotient R).precomp_boundaryImage
    (P.sourceDomainDiskHomeomorph R).symm).trans (P.sourceBoundaryQuotient_boundaryImage R)

theorem sourceDiskBoundaryQuotient_boundary :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      (P.sourceDiskBoundaryQuotient R).boundary = closedBallBoundary := by
  let := P.metricSpace
  intro source R
  ext z
  change ((P.sourceDomainDiskHomeomorph R).symm z).val ∈ frontier R.domain ↔ ‖z.val‖ = 1
  have boundary := (P.sourceRadialBody R).closedBallHomeomorph_boundary_iff
    ((P.sourceDomainDiskHomeomorph R).symm z)
  change (P.sourceDomainDiskHomeomorph R
    ((P.sourceDomainDiskHomeomorph R).symm z)).val ∈ Metric.sphere (0 : Plane) 1 ↔
      ((P.sourceDomainDiskHomeomorph R).symm z).val ∈ frontier R.domain at boundary
  simpa only [Homeomorph.apply_symm_apply, Metric.mem_sphere, dist_zero_right] using boundary.symm

end Unfoldings.SpatialFolding.ConvexBoundary
