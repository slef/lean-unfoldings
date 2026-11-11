module

public import Unfoldings.Cap.ExtendedOutwardForest
public import Unfoldings.Cap.ExtendedComponentSectors
public import Unfoldings.Cap.CompletedSubtreeSectors

/-! Actual extended parent subtrees have derived common five-sector coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- Both the top edge and every positive descendant opening stay in one fixed sector.
This is derived from the original forest and actual roof meshing, without an auxiliary
sector hypothesis. Added flat branches may have arbitrary directions. -/
theorem cornerExtendedOutward_subtree_sectors (positive : 0 < t) (small : t < 1)
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
    ∀ e : {w : L.partition.pairedComplex.Vertex Set.univ //
        w ∉ R.spanningCompletion.parents.roots},
      Q.projectedVertex e.val ∈ M.extendedGeometricCuts F →
        ∃ i : FiveSector,
          Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
            Q.projectedVertex e.val ∈ closedFiveSector t i ∧
          R.CurvedSubtreeInSector (t := t) i e := by
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
  refine fun e member => ?_
  exact R.val.exists_subtree_sector_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered lower)
    (M.exists_cut_component_sector F covered positive small)
    (M.extended_cut_curvature_covered T internal source_height lower conforming height) e member

end Unfoldings.ConvexCap.SectorForest
