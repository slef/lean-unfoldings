module

public import Unfoldings.Source.Unfolding

/-! Exact interior, boundary, and nontrivial-fiber behavior of the source projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceProjection_interior_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.domain),
      z.val ∈ interior R.domain ↔
        R.projection (P.sourcePathCoordinate_injective R) z ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R z
  let H := R.coordinateHomeomorph (P.sourcePathCoordinate_injective R)
  let p := H.symm z
  have vector : R.coordinate p.path p.geodesic = z.val :=
    congrArg Subtype.val (H.apply_symm_apply z)
  have result := P.source_vector_mem_interior_iff_off_cut R p
  rw [vector] at result
  exact result

theorem sourceProjection_boundary_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.domain),
      z.val ∈ frontier R.domain ↔
        R.projection (P.sourcePathCoordinate_injective R) z ∈ sourceCutLocus source := by
  let := P.metricSpace
  intro source R z
  rw [mem_frontier_iff_notMem_interior z.property, P.sourceProjection_interior_iff R z]
  exact not_not

theorem sourceProjection_eq_source_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.domain),
      R.projection (P.sourcePathCoordinate_injective R) z = source ↔ z.val = 0 := by
  let := P.metricSpace
  intro source R z
  have length := R.norm_eq_projection_distance (P.sourcePathCoordinate_injective R) z
  constructor
  · intro equal
    rw [equal, dist_self] at length
    exact norm_eq_zero.mp length
  · intro zero
    rw [zero, norm_zero] at length
    exact (dist_eq_zero.mp length.symm).symm

theorem sourceProjection_fiber_eq_or_boundary :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z w : R.domain),
      R.projection (P.sourcePathCoordinate_injective R) z =
        R.projection (P.sourcePathCoordinate_injective R) w →
      z = w ∨ (z.val ∈ frontier R.domain ∧ w.val ∈ frontier R.domain) := by
  let := P.metricSpace
  intro source R z w equal
  by_cases outside : R.projection (P.sourcePathCoordinate_injective R) z ∉ sourceCutLocus source
  · left
    let H := R.coordinateHomeomorph (P.sourcePathCoordinate_injective R)
    have paths := SourcePath.eq_of_target_eq_off_cutLocus (p := H.symm z) (q := H.symm w)
      outside equal
    exact H.symm.injective paths
  · right
    have cut : R.projection (P.sourcePathCoordinate_injective R) z ∈ sourceCutLocus source :=
      not_not.mp outside
    refine ⟨(P.sourceProjection_boundary_iff R z).mpr cut, ?_⟩
    apply (P.sourceProjection_boundary_iff R w).mpr
    rwa [← equal]

end Unfoldings.SpatialFolding.ConvexBoundary
