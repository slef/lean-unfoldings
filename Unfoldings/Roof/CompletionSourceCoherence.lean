module

public import Unfoldings.Roof.CompletionLeafCoherence
public import Unfoldings.Roof.GeometricLeafAvoidance
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! The planar source has one actual developed value, even when it is not a mesh vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

/-- If the source is not an original vertex, no original parent segment or exterior radial
continuation can pass through it. This uses whole-edge radial monotonicity. -/
theorem source_not_mem_extendedCuts_of_not_original_vertex
    (positive : 0 < t) (small : t < 1) {outer : Set Plane}
    (F : K.SkirtTailFamily outer origin)
    (away : origin ∉ Set.range K.projectedVertex) : origin ∉ M.extendedGeometricCuts F := by
  rintro (original | skirt)
  · obtain ⟨e, member⟩ := Set.mem_iUnion.mp original
    obtain ⟨a, bounds, at_source⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
    have compare := dist_lineMap_le_of_inner_nonneg origin (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val)) (M.parent_radial_outward positive small e)
      (t := 0) (s := a) le_rfl bounds.1
    rw [AffineMap.lineMap_apply_zero, at_source, dist_self] at compare
    have same : origin = K.projectedVertex e.val :=
      dist_eq_zero.mp (le_antisymm compare dist_nonneg)
    exact away ⟨e.val, same.symm⟩
  · obtain ⟨c, member⟩ := Set.mem_iUnion.mp skirt
    exact F.component_outside c member M.inside

variable {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

/-- At an original source vertex use geometric leaf coherence; elsewhere the source is uncut.
No source vertex, extra cut, or local chart agreement is supplied by the caller. -/
theorem completion_source_coherent (positive : 0 < t) (small : t < 1)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    let R := (M.completionOutwardForest E positive small).val
    ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
      origin ∈ L.cap.footprint ∧ D.ProjectedCoherentAt L.cap origin := by
  classical
  let F := E.cornerTails M.inside
  let covered := E.cornerTails_covers_rim M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest E positive small).val
  refine fun D => ⟨?_, ?_⟩
  · rw [L.cap_footprint]
    exact interior_subset (E.covers (Or.inl (interior_subset M.inside)))
  · by_cases original : origin ∈ Set.range K.projectedVertex
    · obtain ⟨w, position⟩ := original
      have nonroot := M.geometric_original_nonroot F covered positive small w
      have childless : ∀ child ∉ (M.geometricParents F covered positive small).roots,
          M.geometricParent F covered child ≠ Sum.inl w := by
        intro child child_nonroot same
        apply M.geometric_origin_childless F covered positive small child child_nonroot
        rw [same]
        exact position
      obtain ⟨_, _, coherent⟩ := M.completion_geometric_leaf_coherent E positive small height
        (Sum.inl w) nonroot childless
      have result := coherent (R.completedDevelopment D)
      change D.ProjectedCoherentAt L.cap (K.projectedVertex w) at result
      rwa [position] at result
    · apply D.projected_coherentAt_of_not_cut L.cap
      intro on_cut
      exact M.source_not_mem_extendedCuts_of_not_original_vertex positive small F original
        (R.projectedCutSet_subset on_cut)

end Unfoldings.ConvexRoof.SectorForest
