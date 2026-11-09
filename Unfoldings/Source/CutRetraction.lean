module

public import Unfoldings.Source.ProjectionFibers
public import Unfoldings.Geometry.RadialRetraction
public import Unfoldings.Topology.QuotientRetraction

/-!
# The source cut locus is a retract of the punctured original surface

Radial retraction of the punctured source disk fixes its boundary. All
nontrivial projection fibers lie on that boundary, so the folded radial map
is constant on every fiber. Quotient descent gives a continuous retraction
on the original surface with only the source removed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_sourceCutLocus_retraction :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ retract : C(↥(({source} : Set (C.Realization Set.univ))ᶜ), sourceCutLocus source),
        ∀ x : sourceCutLocus source, ∀ h : x.val ∈ ({source}ᶜ), retract ⟨x.val, h⟩ = x := by
  let := P.metricSpace
  intro source R
  let projection := R.projection (P.sourcePathCoordinate_injective R)
  let puncture : Set (C.Realization Set.univ) := {source}ᶜ
  let fiber := projection ⁻¹' puncture
  let restricted := puncture.restrictPreimage projection
  let body := P.sourceRadialBody R
  have nonzero (x : fiber) : x.val.val ≠ 0 := by
    intro zero
    have at_source := (P.sourceProjection_eq_source_iff R x.val).mpr zero
    exact x.property at_source
  let into_puncture (x : fiber) : {z : Plane // z ≠ 0} := ⟨x.val.val, nonzero x⟩
  have continuous_puncture : Continuous into_puncture :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let boundary (x : fiber) := body.retractToBoundary (into_puncture x)
  have continuous_boundary : Continuous boundary :=
    body.continuous_retractToBoundary.comp continuous_puncture
  let include_boundary (x : frontier R.domain) : R.domain :=
    ⟨x.val, R.closed_domain.frontier_subset x.property⟩
  have continuous_inclusion : Continuous include_boundary := continuous_subtype_val.subtype_mk _
  let folded (x : fiber) : sourceCutLocus source :=
    ⟨projection (include_boundary (boundary x)),
      (P.sourceProjection_boundary_iff R (include_boundary (boundary x))).mp (boundary x).property⟩
  have continuous_folded : Continuous folded :=
    (((R.continuous_projection (P.sourcePathCoordinate_injective R)).comp continuous_inclusion).comp
      continuous_boundary).subtype_mk _
  have on_boundary (x : fiber) (member : x.val.val ∈ frontier R.domain) :
      (folded x).val = projection x.val := by
    have same : boundary x = (⟨x.val.val, member⟩ : frontier R.domain) :=
      body.retractToBoundary_boundary ⟨x.val.val, member⟩
    change projection (include_boundary (boundary x)) = projection x.val
    rw [same]
  let := isCompact_iff_compactSpace.mp R.compact_domain
  have quotient : Topology.IsQuotientMap projection :=
    Topology.IsQuotientMap.of_surjective_continuous (P.sourceProjection_surjective R)
      (R.continuous_projection (P.sourcePathCoordinate_injective R))
  have restricted_quotient : Topology.IsQuotientMap restricted :=
    quotient.restrictPreimage_isOpen isOpen_compl_singleton
  have fibers : ∀ x y : fiber, restricted x = restricted y → folded x = folded y := by
    intro x y equal
    have image : projection x.val = projection y.val := congrArg Subtype.val equal
    rcases P.sourceProjection_fiber_eq_or_boundary R x.val y.val image with same | ⟨hx, hy⟩
    · exact congrArg folded (Subtype.ext same)
    · apply Subtype.ext
      exact (on_boundary x hx).trans (image.trans (on_boundary y hy).symm)
  let retract := quotientContinuousDesc restricted restricted_quotient
    ⟨folded, continuous_folded⟩ fibers
  refine ⟨retract, ?_⟩
  intro x hx
  obtain ⟨z, image⟩ := P.sourceProjection_surjective R x.val
  change projection z = x.val at image
  have cut : projection z ∈ sourceCutLocus source := by
    rw [image]
    exact x.property
  have member : z.val ∈ frontier R.domain :=
    (P.sourceProjection_boundary_iff R z).mpr cut
  let lift : fiber := ⟨z, by
    change projection z ∈ puncture
    rw [image]
    exact hx⟩
  have lifted : restricted lift = (⟨x.val, hx⟩ : puncture) := Subtype.ext image
  rw [← lifted]
  change quotientContinuousDesc restricted restricted_quotient
    ⟨folded, continuous_folded⟩ fibers (restricted lift) = x
  rw [quotientContinuousDesc_apply]
  apply Subtype.ext
  exact (on_boundary lift member).trans image

end Unfoldings.SpatialFolding.ConvexBoundary
