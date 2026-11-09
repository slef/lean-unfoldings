module

public import Unfoldings.Source.DomainInterior
public import Unfoldings.Source.RegularUnique
public import Unfoldings.Source.PrefixCutAvoidance
public import Unfoldings.Source.RadialDomain
public import Unfoldings.Source.UniqueProjection
public import Unfoldings.Geometry.RadialInterior

/-!
# Exact interior of the actual convex-surface source-vector domain

A source vector is interior precisely when its endpoint is regular and off
the closed source cut locus. The reverse direction constructs an open affine
endpoint patch. For the forward direction, extend the vector slightly outward;
source-vector injectivity identifies it with a proper prefix of the longer
actual shortest path. Prefix regularity and closed-cut avoidance apply.
-/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourcePath_regular_at_proper_time :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (p : SourcePath source)
      (t : unitInterval), t < 1 → C.IsRegularPoint Set.univ (p.path t) := by
  let := P.metricSpace
  intro source R p t before
  have at_source : C.IsRegularPoint Set.univ source :=
    ⟨R.radius, R.positive, R.center, ⟨R.chart⟩⟩
  by_cases same : p.target = source
  · rw [SourcePath.eq_source_of_target_eq same t]
    exact at_source
  by_cases zero : t = 0
  · simpa only [zero, Path.source] using at_source
  have positive : (0 : unitInterval) < t :=
    lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.property.1) (Ne.symm zero)
  exact P.geodesic_isRegularPoint p.geodesic (Ne.symm same) t ⟨positive, before⟩

theorem source_vector_mem_interior_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (p : SourcePath source),
      R.coordinate p.path p.geodesic ∈ interior R.domain ↔
        C.IsRegularPoint Set.univ p.target ∧ p.target ∉ sourceCutLocus source := by
  let := P.metricSpace
  intro source R p
  constructor
  · intro inside
    obtain ⟨scale, greater, member⟩ := exists_gt_one_smul_mem_of_interior inside
    obtain ⟨q, image⟩ := member
    change R.coordinate q.path q.geodesic = scale • R.coordinate p.path p.geodesic at image
    have positive : 0 < scale := zero_lt_one.trans greater
    have inverse_lt : scale⁻¹ < 1 := (inv_lt_one₀ positive).mpr greater
    let t : unitInterval := ⟨scale⁻¹, (inv_pos.mpr positive).le, inverse_lt.le⟩
    have before : t < (1 : unitInterval) := inverse_lt
    have equal_coordinates : P.sourcePathCoordinate R (q.initial t) =
        P.sourcePathCoordinate R p := by
      change R.coordinate (q.initial t).path (q.initial t).geodesic = R.coordinate p.path p.geodesic
      rw [R.coordinate_initial, image, smul_smul]
      change (scale⁻¹ * scale) • R.coordinate p.path p.geodesic = R.coordinate p.path p.geodesic
      rw [inv_mul_cancel₀ positive.ne', one_smul]
    have paths := P.sourcePathCoordinate_injective R equal_coordinates
    have target : q.path t = p.target := congrArg SourcePath.target paths
    have regular := P.sourcePath_regular_at_proper_time R q t before
    have outside := P.sourcePath_proper_prefix_not_cutLocus R q t before
    rw [target] at regular outside
    exact ⟨regular, outside⟩
  · rintro ⟨regular, outside⟩
    have unique : ∀ q : SourcePath source, q.target = p.target → q = p := by
      intro q equal
      exact SourcePath.eq_of_target_eq_off_cutLocus (by rwa [equal]) equal
    exact R.coordinate_mem_interior_domain (P.sourcePath_target_surjective source) p
      (P.sourcePath_all_regular R p regular) unique

theorem sourcePath_proper_prefix_vector_interior :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (p : SourcePath source)
      (t : unitInterval), t < 1 →
        (t : ℝ) • R.coordinate p.path p.geodesic ∈ interior R.domain := by
  let := P.metricSpace
  intro source R p t before
  rw [← R.coordinate_initial p t]
  exact (P.source_vector_mem_interior_iff R (p.initial t)).mpr
    ⟨P.sourcePath_regular_at_proper_time R p t before,
      P.sourcePath_proper_prefix_not_cutLocus R p t before⟩

end Unfoldings.SpatialFolding.ConvexBoundary
