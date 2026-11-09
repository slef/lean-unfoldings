module

public import Unfoldings.Source.ActualCut

/-! The closed source cut locus is a connected image of the net boundary circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceDomain_boundary_projection_cutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.projection (P.sourcePathCoordinate_injective R) ''
        {z : R.domain | z.val ∈ frontier R.domain} = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  rw [P.sourceDomain_boundary_projection R]
  exact P.sourceSlitSet_eq_sourceCutLocus R

theorem sourceCutLocus_isConnected :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      IsConnected (sourceCutLocus source) := by
  let := P.metricSpace
  intro source R
  let H := P.sourceDomainBoundaryHomeomorph R
  let := plane_unit_sphere_connected
  let : ConnectedSpace (frontier R.domain) := H.symm.surjective.connectedSpace H.symm.continuous
  let into (z : frontier R.domain) : R.domain := ⟨z.val, R.closed_domain.frontier_subset z.property⟩
  let projection := R.projection (P.sourcePathCoordinate_injective R) ∘ into
  have continuous_into : Continuous into := continuous_subtype_val.subtype_mk _
  have continuous_projection : Continuous projection :=
    (R.continuous_projection (P.sourcePathCoordinate_injective R)).comp continuous_into
  have image : Set.range projection = sourceCutLocus source := by
    rw [← P.sourceDomain_boundary_projection_cutLocus R]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨into z, z.property, rfl⟩
    · rintro ⟨z, boundary, rfl⟩
      exact ⟨⟨z.val, boundary⟩, rfl⟩
  rw [← image]
  exact isConnected_range continuous_projection

end Unfoldings.SpatialFolding.ConvexBoundary
