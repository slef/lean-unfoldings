module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Roof.CompletionSubtreeSectors

/-! Entire actual fine-seam bank paths inherit one sector from the original cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}

theorem completionOutward_bankChain_sectors (positive : 0 < t) (small : t < 1)
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
        ∃ i : FiveSector, ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
          (Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
            Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
          R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j) := by
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
  exact R.val.exists_completedBankChain_sector_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered)
    (M.exists_cut_component_sector F covered positive small)
    (M.radialMesh_curvature_covered T height) w member

end Unfoldings.ConvexRoof.SectorForest
