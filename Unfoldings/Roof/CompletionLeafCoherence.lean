module

public import Unfoldings.Roof.GeometricLeafMinimum
public import Unfoldings.Roof.GeometricLeafInterior
public import Unfoldings.Roof.CompletionEndpointVertices
public import Unfoldings.Roof.CompletionOutwardForest
public import Unfoldings.Cap.RadialLeafCoherence

/-! Actual geometric leaves survive refinement and have coherent developed endpoint values. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

theorem meshed_geometric_nonroot_vertex (positive : 0 < t) (small : t < 1)
    (w : (E.cornerTails M.inside).GeometricVertex)
    (nonroot : w ∉ (M.geometricParents (E.cornerTails M.inside)
      (E.cornerTails_covers_rim M.inside) positive small).roots) :
    let F := E.cornerTails M.inside
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∃ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
      L.cap.projectedVertex v = F.geometricPosition w ∧
        ¬ L.mesh.toTriangulation.pairedComplex.IsBoundaryVertex Set.univ v := by
  let F := E.cornerTails M.inside
  let covered := E.cornerTails_covers_rim M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let Q := L.cap
  have preserved : ∃ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
      Q.projectedVertex v = F.geometricPosition w := by
    cases w with
    | inl w => exact L.originalPart.original_vertex_preserved w
    | inr w =>
      cases w with
      | inr c => exact (nonroot ⟨c, rfl⟩).elim
      | inl c =>
        let a : F.Active := ⟨c.val, c.property.1⟩
        exact L.mesh.toTriangulation.vertex_of_segment_endpoint L.conforming L.interior_nonempty
          c.property.1 (E.radialMesh_component_cover M.inside a)
  obtain ⟨v, at_vertex⟩ := preserved
  refine ⟨v, at_vertex, (Q.projectedVertex_mem_interior_iff v).mp ?_⟩
  rw [L.cap_footprint, at_vertex]
  exact M.geometric_nonroot_mem_clip_interior F covered positive small w nonroot

/-- Flat completion twigs may give several intrinsic copies at a leaf; all actual placed
values agree. The proof derives this from curvature coverage and local radial minimality. -/
theorem completion_geometric_leaf_coherent (positive : 0 < t) (small : t < 1)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (K.completionPlanes E.tentHeight (Real.sin φ / 2) i).normal 2) :
    let F := E.cornerTails M.inside
    let covered := E.cornerTails_covers_rim M.inside
    let P := M.geometricParents F covered positive small
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    let R := (M.completionOutwardForest E positive small).val
    ∀ leaf : F.GeometricVertex, leaf ∉ P.roots →
      (∀ child ∉ P.roots, M.geometricParent F covered child ≠ leaf) →
      ∃ v : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
        L.cap.projectedVertex v = F.geometricPosition leaf ∧
          ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.completedRetain,
            D.ProjectedCoherentAt L.cap (F.geometricPosition leaf) := by
  let F := E.cornerTails M.inside
  let covered := E.cornerTails_covers_rim M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := M.completionOutwardForest E positive small
  refine fun leaf nonroot childless => ?_
  obtain ⟨v, at_leaf, internal_v⟩ := M.meshed_geometric_nonroot_vertex E positive small leaf nonroot
  change L.cap.projectedVertex v = F.geometricPosition leaf at at_leaf
  have v_nonroot : v ∉ R.val.spanningCompletion.parents.roots := by
    intro root
    exact internal_v ((Set.ext_iff.mp R.val.spanningCompletion.roots_eq v).mp root)
  have minimum := M.geometric_leaf_local_radial_min F covered positive small leaf nonroot childless
  have at_v : ∀ᶠ x in 𝓝 (L.cap.projectedVertex v), x ∈ M.extendedGeometricCuts F →
      dist origin (L.cap.projectedVertex v) ≤ dist origin x := by
    rw [at_leaf]
    exact minimum
  refine ⟨v, at_leaf, fun D => ?_⟩
  have coherent := R.val.projected_coherent_of_local_radial_min D R.property
    (M.radialMesh_curvature_covered E height) v v_nonroot at_v
  change D.ProjectedCoherentAt L.cap (L.cap.projectedVertex v) at coherent
  rw [at_leaf] at coherent
  exact coherent

end Unfoldings.ConvexRoof.SectorForest
