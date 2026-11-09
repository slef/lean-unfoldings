module

public import Unfoldings.Metric.PolygonalCompletion
public import Unfoldings.Metric.PolygonalPaths
public import Unfoldings.Source.DomainDensity
public import Unfoldings.Source.DomainBoundary
public import Unfoldings.Source.InteriorHomeomorph

/-!
# The constructed intrinsic source cut metric and its completion

The flat retained surface receives the polygonal metric through its proved
source-coordinate homeomorphism. The whole shortest-path vector domain,
with its own intrinsic metric, completes this interior. Tied shortest paths
retain their different vectors and hence their different completion points.
The continuous endpoint projection covers the original convex surface, and
its boundary image is exactly the closed cut locus union singular points.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)

abbrev cutInterior := PolygonalPoint (interior R.domain)

abbrev cutCompletion := PolygonalPoint R.domain

def cutInteriorInclusion : R.cutInterior → R.cutCompletion :=
  PolygonalPoint.inclusion interior_subset

def cutCompletionProjection
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    R.cutCompletion → X := R.projection injective ∘ PolygonalPoint.toSubtype

theorem continuous_cutCompletionProjection
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    Continuous (R.cutCompletionProjection injective) :=
  (R.continuous_projection injective).comp PolygonalPoint.continuous_toSubtype

theorem cutCompletionProjection_surjective
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (exists_paths : Function.Surjective (SourcePath.target (source := source))) :
    Function.Surjective (R.cutCompletionProjection injective) := by
  intro x
  obtain ⟨z, equal⟩ := R.projection_surjective injective exists_paths x
  exact ⟨PolygonalPoint.ofSubtype z, equal⟩

omit [CompactSpace X] in
theorem cutCompletion_development_injective :
    Function.Injective (PolygonalPoint.val (s := R.domain)) :=
  fun _ _ equal => PolygonalPoint.ext equal

omit [CompactSpace X] in
theorem cutCompletion_development_lipschitz :
    LipschitzWith 1 (PolygonalPoint.val (s := R.domain)) := PolygonalPoint.ambient_lipschitz

end Unfoldings.SourceFrame

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceCutSurfaceHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      sourceRegularRegion source ≃ₜ R.cutInterior := by
  let := P.metricSpace
  intro source R
  exact (P.sourceInteriorHomeomorph R).trans
    (PolygonalPoint.openHomeomorph isOpen_interior).symm

def sourceCutCompletionModel :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      AbstractCompletion R.cutInterior := by
  let := P.metricSpace
  intro source R
  exact PolygonalPoint.interiorCompletion R.starConvex_domain
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht) R.compact_domain

theorem sourceCutInteriorInclusion_isometry :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      Isometry R.cutInteriorInclusion := by
  let := P.metricSpace
  intro source R
  exact PolygonalPoint.interior_inclusion_isometry
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht)

theorem sourceCutInteriorInclusion_dense :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      DenseRange R.cutInteriorInclusion := by
  let := P.metricSpace
  intro source R
  exact PolygonalPoint.interior_inclusion_dense R.starConvex_domain
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht)

theorem sourceCutCompletion_compact :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      CompactSpace R.cutCompletion := by
  let := P.metricSpace
  intro source R
  exact PolygonalPoint.compactSpace_of_radial_interior R.starConvex_domain
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht) R.compact_domain

theorem sourceCutCompletion_complete :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      CompleteSpace R.cutCompletion := by
  let := P.metricSpace
  intro source R
  exact PolygonalPoint.completeSpace_of_radial_interior R.starConvex_domain
    (fun z hz t ht => P.sourceDomain_radial_interior R hz t ht) R.compact_domain

@[instance_reducible] def sourceCutCompletedMetric :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      MetricSpace R.cutCompletion := by
  let := P.metricSpace
  intro source R
  exact EMetricSpace.toMetricSpace
    (PolygonalPoint.edist_ne_top_of_starConvex R.starConvex_domain R.zero_mem_domain)

@[instance_reducible] def sourceCutInteriorMetric :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      MetricSpace R.cutInterior := by
  let := P.metricSpace
  intro source R
  have zero : (0 : Plane) ∈ interior R.domain := by
    simpa only [Set.Icc.coe_zero, zero_smul] using
      P.sourceDomain_radial_interior R R.zero_mem_domain 0 zero_lt_one
  exact EMetricSpace.toMetricSpace
    (PolygonalPoint.edist_ne_top_of_starConvex (P.sourceDomain_interior_starConvex R) zero)

theorem sourceCutCompletion_boundary_projection :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.cutCompletionProjection (P.sourcePathCoordinate_injective R) ''
        {z : R.cutCompletion | z.val ∈ frontier R.domain} = sourceSlitSet source := by
  let := P.metricSpace
  intro source R
  rw [← P.sourceDomain_boundary_projection_slitSet R]
  ext x
  constructor
  · rintro ⟨z, boundary, rfl⟩
    exact ⟨PolygonalPoint.toSubtype z, boundary, rfl⟩
  · rintro ⟨z, boundary, rfl⟩
    exact ⟨PolygonalPoint.ofSubtype z, boundary, rfl⟩

end Unfoldings.SpatialFolding.ConvexBoundary
