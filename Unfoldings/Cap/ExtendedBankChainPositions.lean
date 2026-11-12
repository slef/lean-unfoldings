module

public import Unfoldings.Cap.ExtendedBankChains
public import Unfoldings.Cap.CompletedBankChainPositions
public import Unfoldings.Cap.GeometricComponentPieces

/-! Actual fine cut paths inherit source positions and bank-opening sectors together. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- The actual original-plus-roof component chooses one common sector for every
fine path vertex, every outward path direction, and every curved descendant opening. -/
theorem cornerExtendedOutward_bankChain_sector_positions (positive : 0 < t) (small : t < 1)
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
        ∃ i : FiveSector,
          (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
            (Q.projectedVertex
              (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
                Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
            R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j)) ∧
          ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
            (R.completedRootPath w).vertex j - K.projectedVertex origin ∈ closedFiveSector t i := by
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
  apply R.val.exists_completedBankChain_sector_positions_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered lower) ?_
    (M.extended_cut_curvature_covered T internal source_height lower conforming height) w member
  intro c
  let data := M.geometricComponentSector F covered positive small lower c
  exact ⟨data.sector, fun j same => (data.cut_piece_geometry j same).1,
    fun j same => (data.cut_piece_geometry j same).2⟩

end Unfoldings.ConvexCap.SectorForest
