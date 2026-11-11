module

public import Unfoldings.Cap.FlatDescendantCopies
public import Unfoldings.Cap.CompletedSubtreeDirections
public import Unfoldings.Geometry.SegmentLocalMinimum

/-! Local radial minima of the prescribed cut set have one developed endpoint value. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem parent_ne_local_radial_min (outward : R.Outward) (v : C.Vertex Set.univ)
    (minimum : ∀ᶠ x in 𝓝 (K.projectedVertex v), x ∈ cuts →
      dist q (K.projectedVertex v) ≤ dist q x)
    (w : C.Vertex Set.univ) (nonroot : w ∉ R.parents.roots) : R.parents.parent w ≠ v := by
  intro same
  have different : K.projectedVertex w ≠ K.projectedVertex (R.parents.parent w) := by
    intro equal
    have vertices := K.projectedVertex_injective equal
    have ascending := R.parents.ascending w nonroot
    rw [← vertices] at ascending
    exact lt_irrefl _ ascending
  have subset : segment ℝ (K.projectedVertex w)
      (K.projectedVertex (R.parents.parent w)) ⊆ cuts :=
    (K.selected_parent_segment_eq_seam R.selection ⟨w, nonroot⟩).subset.trans
      (R.selected_subset ⟨w, nonroot⟩)
  have nearby_minimum := minimum
  rw [← same] at nearby_minimum
  exact outward_segment_endpoint_not_local_min (outward w nonroot) different subset nearby_minimum

/-- Flat completion branches may enter a geometric leaf, but positive curvature cannot. -/
theorem proper_subtrees_flat_of_local_radial_min (outward : R.Outward)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (v : C.Vertex Set.univ) (nonroot : v ∉ R.spanningCompletion.parents.roots)
    (minimum : ∀ᶠ x in 𝓝 (K.projectedVertex v), x ∈ cuts →
      dist q (K.projectedVertex v) ≤ dist q x)
    (z : C.Vertex Set.univ) (ancestor : R.spanningCompletion.parents.Ancestor z v)
    (different : z ≠ v) : R.completedSubtreeCurvature z = 0 := by
  apply le_antisymm _ (R.completedSubtreeCurvature_nonneg z)
  by_contra positive
  have member := R.mem_cuts_of_completedSubtreeCurvature_pos covered z (lt_of_not_ge positive)
  obtain ⟨n, reaches⟩ := ancestor
  cases n with
  | zero => exact different reaches
  | succ n =>
    let P := R.spanningCompletion.parents
    let u := P.parent^[n] z
    have parent : P.parent u = v := by
      simpa only [Function.iterate_succ_apply'] using reaches
    have u_nonroot : u ∉ P.roots := by
      intro root
      have equal : u = v := (P.fixed_root u root).symm.trans parent
      exact nonroot (equal ▸ root)
    have u_member : K.projectedVertex u ∈ cuts :=
      R.completed_ancestor_mem_cuts member ⟨n, rfl⟩
    have old_nonroot := R.completed_parent_original_nonroot ⟨u, u_nonroot⟩ u_member
    have old_parent : R.parents.parent u = v := by
      rw [← R.spanningCompletion.parent_eq u old_nonroot]
      exact parent
    exact R.parent_ne_local_radial_min outward v minimum u old_nonroot old_parent

/-- The constructed actual map is coherent at geometric leaf pinches, even with redundant
flat branches. This gives equality of all developed values while keeping intrinsic copies. -/
theorem projected_coherent_of_local_radial_min (D : FacewiseDevelopment C R.completedRetain)
    (outward : R.Outward)
    (covered : ∀ w : C.Vertex Set.univ, 0 < C.interiorAngularDefect Set.univ w →
      K.projectedVertex w ∈ cuts)
    (v : C.Vertex Set.univ) (nonroot : v ∉ R.spanningCompletion.parents.roots)
    (minimum : ∀ᶠ x in 𝓝 (K.projectedVertex v), x ∈ cuts →
      dist q (K.projectedVertex v) ≤ dist q x) :
    D.ProjectedCoherentAt K (K.projectedVertex v) :=
  R.projected_coherent_of_flat_proper_descendants D ⟨v, nonroot⟩
    (R.proper_subtrees_flat_of_local_radial_min outward covered v nonroot minimum)

end Unfoldings.ConvexCap.RadialCutForest
