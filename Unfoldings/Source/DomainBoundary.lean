module

public import Unfoldings.Source.ConvexDomainInterior
public import Unfoldings.Source.ConvexDomain
public import Unfoldings.Source.RegularRegion
public import Unfoldings.Polyhedron.RegularClassification

/-!
# The exact boundary projection of the constructed source domain

The planar boundary projects exactly onto the union of the closed source cut
locus and the singular points. The regular-point classification identifies
the latter as true extreme vertex points. Equality of this union with the
closure-of-ties locus alone is a separate remaining cone-leaf theorem.
-/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceDomain_boundary_iff :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : R.domain),
      z.val ∈ frontier R.domain ↔
        R.projection (P.sourcePathCoordinate_injective R) z ∈ sourceCutLocus source ∨
          ¬ C.IsRegularPoint Set.univ (R.projection (P.sourcePathCoordinate_injective R) z) := by
  let := P.metricSpace
  intro source R z
  classical
  let H := R.coordinateHomeomorph (P.sourcePathCoordinate_injective R)
  let p := H.symm z
  have image : R.coordinate p.path p.geodesic = z.val := congrArg Subtype.val (H.apply_symm_apply z)
  have inside : z.val ∈ interior R.domain ↔
      C.IsRegularPoint Set.univ p.target ∧ p.target ∉ sourceCutLocus source := by
    rw [← image]
    exact P.source_vector_mem_interior_iff R p
  change z.val ∈ frontier R.domain ↔ p.target ∈ sourceCutLocus source ∨
    ¬ C.IsRegularPoint Set.univ p.target
  rw [mem_frontier_iff_notMem_interior z.property, inside, not_and_or, not_not, or_comm]

theorem sourceDomain_boundary_projection :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.projection (P.sourcePathCoordinate_injective R) ''
        {z : R.domain | z.val ∈ frontier R.domain} =
      sourceCutLocus source ∪ {x | ¬ C.IsRegularPoint Set.univ x} := by
  let := P.metricSpace
  intro source R
  ext x
  constructor
  · rintro ⟨z, boundary, rfl⟩
    exact (P.sourceDomain_boundary_iff R z).mp boundary
  · intro bad
    obtain ⟨p, target⟩ := P.sourcePath_target_surjective source x
    let z := R.coordinateHomeomorph (P.sourcePathCoordinate_injective R) p
    have image : R.projection (P.sourcePathCoordinate_injective R) z = x :=
      (R.projection_coordinateHomeomorph (P.sourcePathCoordinate_injective R) p).trans target
    have boundary : z.val ∈ frontier R.domain := by
      apply (P.sourceDomain_boundary_iff R z).mpr
      rwa [image]
    exact ⟨z, boundary, image⟩

theorem sourceDomain_boundary_projection_slitSet :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.projection (P.sourcePathCoordinate_injective R) ''
        {z : R.domain | z.val ∈ frontier R.domain} = sourceSlitSet source := by
  let := P.metricSpace
  intro source R
  exact P.sourceDomain_boundary_projection R

theorem extreme_vertex_mem_source_boundary_image :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (v : C.Vertex Set.univ),
      F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ →
        C.vertexPoint Set.univ v ∈ R.projection (P.sourcePathCoordinate_injective R) ''
          {z : R.domain | z.val ∈ frontier R.domain} := by
  let := P.metricSpace
  intro source R v extreme
  rw [P.sourceDomain_boundary_projection]
  exact Or.inr (fun regular => P.regular_vertex_not_extreme v regular extreme)

end Unfoldings.SpatialFolding.ConvexBoundary
