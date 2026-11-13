module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionBankChains
public import Unfoldings.Cap.CompletedBankChainPositions
public import Unfoldings.Roof.GeometricComponentPieces

/-! Actual fine cut paths inherit source positions and bank-opening sectors together. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}

/-- The actual original-plus-roof component chooses one common sector for every
fine path vertex, every outward path direction, and every curved descendant opening. -/
theorem completionOutward_bankChain_sector_positions (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (T.supportPlanes i).normal 2) :
    let inside := M.inside
    let F := T.cornerTails inside
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let Q := L.cap
    let R := (M.completionOutwardForest T positive small).val
    ∀ w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
      Q.projectedVertex w ∈ M.extendedGeometricCuts F →
        ∃ i : FiveSector,
          (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
            (Q.projectedVertex
              (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
                Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
            R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j)) ∧
          ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
            (R.completedRootPath w).vertex j - origin ∈ closedFiveSector t i := by
  let inside := M.inside
  let F := T.cornerTails inside
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  let R := M.completionOutwardForest T positive small
  have covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
    T.cornerTails_covers_rim inside
  refine fun w member => ?_
  apply R.val.exists_completedBankChain_sector_positions_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered) ?_
    (M.radialMesh_curvature_covered T height) w member
  intro c
  let data := M.geometricComponentSector F covered positive small c
  exact ⟨data.sector, fun j same => (data.cut_piece_geometry j same).1,
    fun j same => (data.cut_piece_geometry j same).2⟩

end Unfoldings.ConvexRoof.SectorForest
