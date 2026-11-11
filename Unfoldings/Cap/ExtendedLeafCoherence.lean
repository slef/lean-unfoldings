module

public import Unfoldings.Cap.GeometricLeafMinimum
public import Unfoldings.Cap.GeometricLeafInterior
public import Unfoldings.Cap.RadialLeafCoherence
public import Unfoldings.Cap.ExtendedPathWedges
public import Unfoldings.Cap.ClipEndpointVertices

/-! Every actual geometric leaf survives roof meshing and has a coherent developed endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

theorem meshed_geometric_nonroot_vertex
    (F : K.SkirtTailFamily Z (K.projectedVertex origin))
    (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (positive : 0 < t) (small : t < 1) (lower : Z < 0) (T : K.ClipSpatialTriangles Z)
    (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots) :
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∃ v : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex v = F.geometricPosition w ∧
        ¬ L.partition.pairedComplex.IsBoundaryVertex Set.univ v := by
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  have preserved : ∃ v : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex v = F.geometricPosition w := by
    cases w with
    | inl w => exact L.originalPart.original_vertex_preserved lower w
    | inr w =>
      cases w with
      | inr c => exact (nonroot ⟨c, rfl⟩).elim
      | inl c =>
        let a : F.Active := ⟨c.val, c.property.1⟩
        exact L.partition.vertex_of_segment_endpoint L.conforming lower c.property.1
          (L.segment_eq_union_subedges a (F.component_member c.val) (F.component_tip_member c.val))
  obtain ⟨v, at_vertex⟩ := preserved
  refine ⟨v, at_vertex, (Q.projectedVertex_mem_interior_iff v).mp ?_⟩
  rw [L.partition.normalizedCap_footprint L.conforming lower, at_vertex]
  exact M.geometric_nonroot_mem_clip_interior F covered positive small lower w nonroot

/-- Every geometric leaf has one developed value in the actual fine roof, even if arbitrary
flat completion branches create several intrinsic copies at that endpoint. -/
theorem cornerExtended_geometric_leaf_coherent (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let P := M.geometricParents F covered positive small lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ leaf : F.GeometricVertex, leaf ∉ P.roots →
      (∀ child ∉ P.roots, M.geometricParent F covered child ≠ leaf) →
      ∃ v : L.partition.pairedComplex.Vertex Set.univ,
        Q.projectedVertex v = F.geometricPosition leaf ∧
          ∀ D : FacewiseDevelopment L.partition.pairedComplex R.completedRetain,
            D.ProjectedCoherentAt Q (F.geometricPosition leaf) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := M.cornerExtendedOutwardForest positive small T internal source_height lower
  refine fun leaf nonroot childless => ?_
  obtain ⟨v, at_leaf, internal_v⟩ := M.meshed_geometric_nonroot_vertex F covered positive small
    lower T leaf nonroot
  change Q.projectedVertex v = F.geometricPosition leaf at at_leaf
  have v_nonroot : v ∉ R.val.spanningCompletion.parents.roots := by
    intro root
    exact internal_v ((Set.ext_iff.mp R.val.spanningCompletion.roots_eq v).mp root)
  have minimum := M.geometric_leaf_local_radial_min F covered positive small lower leaf nonroot
    childless
  have at_v : ∀ᶠ x in 𝓝 (Q.projectedVertex v), x ∈ M.extendedGeometricCuts F →
      dist (K.projectedVertex origin) (Q.projectedVertex v) ≤
        dist (K.projectedVertex origin) x := by
    rw [at_leaf]
    exact minimum
  have curvature_covered := M.extended_cut_curvature_covered T internal source_height lower
    conforming height
  refine ⟨v, at_leaf, fun D => ?_⟩
  have coherent := R.val.projected_coherent_of_local_radial_min D R.property curvature_covered v
    v_nonroot at_v
  change D.ProjectedCoherentAt Q (Q.projectedVertex v) at coherent
  rw [at_leaf] at coherent
  exact coherent

end Unfoldings.ConvexCap.SectorForest
