module

public import Unfoldings.Source.BoundarySegments

/-!
# The actual closed source cut locus is a finite straight network on the surface

Project the exact finite boundary-segment cover through its proved whole-face
rigid maps. This yields an exact finite union of spatial segments, each lying
in one original triangle. Cone leaves and degenerate segment pieces are kept.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_finite_source_cut_segments :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ edges : Set (Space × Space), edges.Finite ∧
        F.toSpace Set.univ '' sourceCutLocus source = ⋃ e ∈ edges, segment ℝ e.1 e.2 ∧
        ∀ e ∈ edges, ∃ f : Face, segment ℝ e.1 e.2 ⊆
          (F.place f) '' (C.triangle f).carrier := by
  let := P.metricSpace
  intro source R
  obtain ⟨boundary_edges, finite_boundary, boundary_cover, formulas⟩ :=
    P.exists_finite_source_boundary_segments R
  let := finite_boundary.fintype
  have specifications (e : boundary_edges) :
      ∃ (f : Face) (A : Plane ≃ᵃⁱ[ℝ] Plane), ∀ z : R.domain,
        z.val ∈ segment ℝ e.val.1 e.val.2 → ∃ y : C.Cell f, z.val = A y.val ∧
          R.projection (P.sourcePathCoordinate_injective R) z = C.faceMap Set.univ f y :=
    formulas e.val e.property
  choose face motion formula using specifications
  let spatial (e : boundary_edges) : Plane →ᵃ[ℝ] Space :=
    (F.place (face e)).toAffineMap.comp (motion e).symm.toAffineMap
  have on_boundary (e : boundary_edges) {x : Plane}
      (member : x ∈ segment ℝ e.val.1 e.val.2) : x ∈ frontier R.domain := by
    rw [boundary_cover]
    exact Set.mem_iUnion₂.mpr ⟨e.val, e.property, member⟩
  have agreement (e : boundary_edges) (z : R.domain)
      (member : z.val ∈ segment ℝ e.val.1 e.val.2) :
      spatial e z.val =
        F.toSpace Set.univ (R.projection (P.sourcePathCoordinate_injective R) z) := by
    obtain ⟨y, developed, image⟩ := formula e z member
    change F.place (face e) ((motion e).symm z.val) = _
    rw [developed, (motion e).symm_apply_apply, image, F.toSpace_faceMap]
  let endpoints (e : boundary_edges) := (spatial e e.val.1, spatial e e.val.2)
  let edges := Set.range endpoints
  refine ⟨edges, Set.finite_range _, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, cut, rfl⟩
      rw [← P.sourceDomain_boundary_projection_cutLocus R] at cut
      obtain ⟨z, boundary, image⟩ := cut
      obtain ⟨e, he, member⟩ := Set.mem_iUnion₂.mp (boundary_cover ▸ boundary)
      let edge : boundary_edges := ⟨e, he⟩
      have mapped : spatial edge z.val ∈ segment ℝ (spatial edge e.1) (spatial edge e.2) := by
        rw [← image_segment ℝ (spatial edge)]
        exact ⟨z.val, member, rfl⟩
      rw [agreement edge z member, image] at mapped
      exact Set.mem_iUnion₂.mpr ⟨endpoints edge, ⟨edge, rfl⟩, mapped⟩
    · intro hx
      obtain ⟨_, ⟨e, rfl⟩, member⟩ := Set.mem_iUnion₂.mp hx
      change x ∈ segment ℝ (spatial e e.val.1) (spatial e e.val.2) at member
      rw [← image_segment ℝ (spatial e)] at member
      obtain ⟨z, on_edge, equal⟩ := member
      let point : R.domain := ⟨z, R.closed_domain.frontier_subset (on_boundary e on_edge)⟩
      have cut : R.projection (P.sourcePathCoordinate_injective R) point ∈
          sourceCutLocus source := by
        rw [← P.sourceDomain_boundary_projection_cutLocus R]
        exact ⟨point, on_boundary e on_edge, rfl⟩
      exact ⟨_, cut, (agreement e point on_edge).symm.trans equal⟩
  · rintro _ ⟨e, rfl⟩
    refine ⟨face e, ?_⟩
    intro x member
    change x ∈ segment ℝ (spatial e e.val.1) (spatial e e.val.2) at member
    rw [← image_segment ℝ (spatial e)] at member
    obtain ⟨z, on_edge, equal⟩ := member
    let point : R.domain := ⟨z, R.closed_domain.frontier_subset (on_boundary e on_edge)⟩
    obtain ⟨y, developed, _⟩ := formula e point on_edge
    refine ⟨y.val, y.property, ?_⟩
    have inverse : (motion e).symm z = y.val := by
      change z = motion e y.val at developed
      rw [developed, (motion e).symm_apply_apply]
    change F.place (face e) y.val = x
    have formula : spatial e z = F.place (face e) y.val := by
      change F.place (face e) ((motion e).symm z) = _
      rw [inverse]
    exact formula.symm.trans equal

end Unfoldings.SpatialFolding.ConvexBoundary
