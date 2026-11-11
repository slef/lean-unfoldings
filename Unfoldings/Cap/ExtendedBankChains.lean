module

public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Cap.ExtendedSubtreeSectors

/-! Entire actual fine-seam bank paths inherit one sector from the original cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

theorem cornerExtendedOutward_bankChain_sectors (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let Q := L.partition.normalizedCap L.conforming lower
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ w : L.partition.pairedComplex.Vertex Set.univ,
      Q.projectedVertex w ∈ M.extendedGeometricCuts F →
        ∃ i : FiveSector, ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
          (Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
            Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
          R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let R := M.cornerExtendedOutwardForest positive small T internal source_height lower
  have covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
    T.cornerTails_covers_rim inside source_height lower
  refine fun w member => ?_
  exact R.val.exists_completedBankChain_sector_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered lower)
    (M.exists_cut_component_sector F covered positive small)
    (M.extended_cut_curvature_covered T internal source_height lower conforming height) w member

end Unfoldings.ConvexCap.SectorForest
