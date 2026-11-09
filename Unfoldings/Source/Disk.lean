module

public import Unfoldings.Geometry.RadialCone
public import Unfoldings.Source.CutMetric

/-!
# The constructed completed source cut surface is a disk

The actual source domain satisfies the hypotheses of the general radial-body
theorem. Its boundary is a circle, and its intrinsic completion is
homeomorphic to the closed unit disk. Finite polygonality and identification
of singular slit endpoints with the closure-of-ties locus are separate tasks.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceRadialBody :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) → RadialBody Plane := by
  let := P.metricSpace
  intro source R
  exact
    { carrier := R.domain
      compact := R.compact_domain
      zero_interior := by
        simpa only [Set.Icc.coe_zero, zero_smul] using
          P.sourceDomain_radial_interior R R.zero_mem_domain 0 zero_lt_one
      radial_interior := fun z hz t ht => P.sourceDomain_radial_interior R hz t ht }

def sourceDomainBoundaryHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      frontier R.domain ≃ₜ Metric.sphere (0 : Plane) 1 := by
  let := P.metricSpace
  intro source R
  exact (P.sourceRadialBody R).boundaryHomeomorph

def sourceDomainDiskHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      R.domain ≃ₜ Metric.closedBall (0 : Plane) 1 := by
  let := P.metricSpace
  intro source R
  exact (P.sourceRadialBody R).closedBallHomeomorph

def sourceCutDiskHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      R.cutCompletion ≃ₜ Metric.closedBall (0 : Plane) 1 := by
  let := P.metricSpace
  intro source R
  exact (PolygonalPoint.radialHomeomorph R.starConvex_domain
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht) R.compact_domain.isBounded).trans
      (P.sourceDomainDiskHomeomorph R)

theorem sourceCutDiskHomeomorph_boundary_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.cutCompletion),
      (P.sourceCutDiskHomeomorph R z).val ∈ Metric.sphere (0 : Plane) 1 ↔
        z.val ∈ frontier R.domain := by
  let := P.metricSpace
  intro source R z
  exact (P.sourceRadialBody R).closedBallHomeomorph_boundary_iff (PolygonalPoint.toSubtype z)

end Unfoldings.SpatialFolding.ConvexBoundary
