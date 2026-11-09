module

public import Unfoldings.Source.ConvexDomainInterior
public import Mathlib.Analysis.Convex.Topology

/-! Every proper radial prefix is interior, and the source domain is the closure of its interior. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceDomain_radial_interior :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) {z : Plane}, z ∈ R.domain →
      ∀ t : unitInterval, t < 1 → (t : ℝ) • z ∈ interior R.domain := by
  let := P.metricSpace
  intro source R z member t before
  obtain ⟨p, rfl⟩ := member
  exact P.sourcePath_proper_prefix_vector_interior R p t before

theorem sourceDomain_closure_interior :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      closure (interior R.domain) = R.domain := by
  let := P.metricSpace
  intro source R
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset R.closed_domain
  · intro z member
    have segment : openSegment ℝ (0 : Plane) z ⊆ interior R.domain := by
      intro y hy
      obtain ⟨t, ht, equal⟩ := (openSegment_eq_image_lineMap ℝ (0 : Plane) z).le hy
      let time : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
      have inside := P.sourceDomain_radial_interior R member time ht.2
      have expression : AffineMap.lineMap (0 : Plane) z t = t • z := by
        simp only [AffineMap.lineMap_apply_module', sub_zero, add_zero]
      rw [expression] at equal
      exact equal ▸ inside
    exact (closure_mono segment) (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))

theorem sourceDomain_interior_starConvex :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      StarConvex ℝ (0 : Plane) (interior R.domain) := by
  let := P.metricSpace
  intro source R z member a b _ha hb sum
  by_cases full : b = 1
  · simpa only [smul_zero, zero_add, full, one_smul] using member
  · have before : b < 1 := lt_of_le_of_ne (by linarith) full
    let t : unitInterval := ⟨b, hb, before.le⟩
    simpa only [smul_zero, zero_add] using
      P.sourceDomain_radial_interior R (interior_subset member) t before

end Unfoldings.SpatialFolding.ConvexBoundary
