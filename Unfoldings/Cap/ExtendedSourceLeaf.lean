module

public import Unfoldings.Cap.ExtendedPathWedges
public import Unfoldings.Cap.ClipEndpointVertices
public import Unfoldings.Cap.RadialSourceLeaf

/-! The actual original source survives roof meshing and remains a leaf after forest completion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Actual original-edge endpoint coverage constructs the source vertex in the fine roof complex. -/
theorem cornerExtended_source_vertex (T : K.ClipSpatialTriangles Z)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∃ source : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex source = K.projectedVertex origin ∧
        ¬ L.partition.pairedComplex.IsBoundaryVertex Set.univ source := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  have preserved : ∃ source : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex source = K.projectedVertex origin :=
    L.originalPart.original_vertex_preserved lower origin
  obtain ⟨source, at_source⟩ := preserved
  refine ⟨source, at_source, (Q.projectedVertex_mem_interior_iff source).mp ?_⟩
  rw [L.partition.normalizedCap_footprint L.conforming lower, at_source]
  exact K.original_footprint_in_clip_interior lower (K.projectedVertex_mem_footprint origin)

/-- The source is a genuine interior leaf of the actual completed fine-seam forest. -/
theorem cornerExtended_source_leaf (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∃ source : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex source = K.projectedVertex origin ∧
        ¬ L.partition.pairedComplex.IsBoundaryVertex Set.univ source ∧
          R.spanningCompletion.parents.descendants source = {source} := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  obtain ⟨source, at_source, source_internal⟩ := cornerExtended_source_vertex T internal
    source_height lower
  exact ⟨source, at_source, source_internal,
    R.completed_descendants_source at_source source_internal⟩

end Unfoldings.ConvexCap.SectorForest
