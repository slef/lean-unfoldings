module

public import Unfoldings.Cap.OriginalCutRestriction
public import Unfoldings.Cap.RadialCutForest
public import Unfoldings.Cap.ClippedCapCoordinates

/-! Any selected auxiliary radial forest retains all fine seams required by the original cut cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} {q : Plane}

open Classical in
theorem extendedOriginalRetain_subset_radial (T : K.ClipSpatialTriangles Z)
    (F : K.SkirtTailFamily Z q) (lower : Z < 0) :
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ R : Q.RadialCutForest q (M.extendedGeometricCuts F),
      L.originalPart.originalRetain M.retain ⊆
        L.partition.pairedComplex.restrictRetain L.originalPart.originalPieceSet R.retain := by
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  change ∀ R : Q.RadialCutForest q (M.extendedGeometricCuts F),
    L.originalPart.originalRetain M.retain ⊆
      L.partition.pairedComplex.restrictRetain L.originalPart.originalPieceSet R.retain
  intro R s kept
  change s.val ∉ Set.range R.selection.edge
  rintro ⟨e, chosen⟩
  have selected := R.selected_subset e
  rw [chosen] at selected
  have kept_network : s.val ∈ M.extendedRetain T F lower := by
    have equal := M.extendedRetain_restrict_original_eq T F lower
    have kept' : s ∈ L.partition.pairedComplex.restrictRetain
        L.originalPart.originalPieceSet (M.extendedRetain T F lower) := equal.symm ▸ kept
    exact kept'
  apply kept_network
  exact (L.partition.normalizedCap_projectedTriangle_edge L.conforming lower
    (L.partition.pairedComplex.left s.val).face
    (L.partition.pairedComplex.left s.val).edge).symm.subset.trans selected

end Unfoldings.ConvexCap.SectorForest
