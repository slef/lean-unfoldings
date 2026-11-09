module

public import Unfoldings.Source.Disk
public import Unfoldings.Geometry.PlaneSphere
public import Unfoldings.Topology.PerfectProjection

/-!
# Singular cone endpoints belong to the closed source cut locus

The source-net boundary is a circle. Outside the closed cut locus its
endpoint projection has singleton fibers, and the only possible boundary
images are finitely many singular vertices. Perfectness of the circle rules
out such a finite open boundary neighborhood. Thus all boundary images,
including unique cone-leaf endpoints, lie in the closure of actual ties.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceBoundary_projection_subset_cutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      R.projection (P.sourcePathCoordinate_injective R) ''
        {z : R.domain | z.val ∈ frontier R.domain} ⊆ sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  let H := P.sourceDomainBoundaryHomeomorph R
  let := plane_unit_sphere_connected
  let := plane_unit_sphere_nontrivial
  let : ConnectedSpace (frontier R.domain) := H.symm.surjective.connectedSpace H.symm.continuous
  let : Nontrivial (frontier R.domain) := H.symm.injective.nontrivial
  let : PerfectSpace (frontier R.domain) := inferInstance
  let into (z : frontier R.domain) : R.domain := ⟨z.val, R.closed_domain.frontier_subset z.property⟩
  let path (z : frontier R.domain) := (P.sourceDomainHomeomorph R).symm (into z)
  let f (z : frontier R.domain) := (path z).target
  have continuous_into : Continuous into := continuous_subtype_val.subtype_mk _
  have continuous_f : Continuous f := SourcePath.continuous_target.comp
    ((P.sourceDomainHomeomorph R).symm.continuous.comp continuous_into)
  have images : Set.range f ⊆ sourceCutLocus source ∪ Set.range (C.vertexPoint Set.univ) := by
    rintro _ ⟨z, rfl⟩
    have boundary := (P.sourceDomain_boundary_iff R (into z)).mp z.property
    rcases boundary with cut | singular
    · exact Or.inl cut
    · apply Or.inr
      by_contra not_vertex
      apply singular
      apply P.isRegularPoint_of_ne_extreme_vertices
      intro v _extreme equal
      exact not_vertex ⟨v, equal.symm⟩
  have unique (a b : frontier R.domain) (outside : f a ∉ sourceCutLocus source)
      (equal : f a = f b) : a = b := by
    have paths : path a = path b := SourcePath.eq_of_target_eq_off_cutLocus outside equal
    have points : into a = into b := (P.sourceDomainHomeomorph R).symm.injective paths
    apply Subtype.ext
    exact congrArg (fun w : R.domain => w.val) points
  have range_cut := range_subset_closed_of_perfect f continuous_f
    (isClosed_sourceCutLocus source) (Set.finite_range (C.vertexPoint Set.univ)) images unique
  rintro _ ⟨z, boundary, rfl⟩
  exact range_cut ⟨⟨z.val, boundary⟩, rfl⟩

theorem singular_point_mem_sourceCutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source)
      (x : C.Realization Set.univ), ¬ C.IsRegularPoint Set.univ x → x ∈ sourceCutLocus source := by
  let := P.metricSpace
  intro source R x singular
  apply P.sourceBoundary_projection_subset_cutLocus R
  rw [P.sourceDomain_boundary_projection R]
  exact Or.inr singular

theorem extreme_vertex_mem_sourceCutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source) (v : C.Vertex Set.univ),
      F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ →
        C.vertexPoint Set.univ v ∈ sourceCutLocus source := by
  let := P.metricSpace
  intro source R v extreme
  exact P.singular_point_mem_sourceCutLocus R _
    (fun regular => P.regular_vertex_not_extreme v regular extreme)

theorem sourceSlitSet_eq_sourceCutLocus :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      sourceSlitSet source = sourceCutLocus source := by
  let := P.metricSpace
  intro source R
  apply Set.Subset.antisymm
  · intro x member
    exact member.elim id (P.singular_point_mem_sourceCutLocus R x)
  · exact Set.subset_union_left

end Unfoldings.SpatialFolding.ConvexBoundary
