module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionOutwardForest
public import Unfoldings.Roof.ExtendedComponentSectors
public import Unfoldings.Cap.CompletedSubtreeSectors

/-! Actual extended parent subtrees have derived common five-sector coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}

/-- Both the top edge and every positive descendant opening stay in one fixed sector.
This is derived from the original forest and actual roof meshing, without an auxiliary
sector hypothesis. Added flat branches may have arbitrary directions. -/
theorem completionOutward_subtree_sectors (positive : 0 < t) (small : t < 1)
    (T : K.CompletionMesh φ region extra)
    (height : ∀ i, (3 : ℝ) / 4 ≤ (T.supportPlanes i).normal 2) :
    let inside := M.inside
    let F := T.cornerTails inside
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
    let Q := L.cap
    let R := (M.completionOutwardForest T positive small).val
    ∀ e : {w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ //
        w ∉ R.spanningCompletion.parents.roots},
      Q.projectedVertex e.val ∈ M.extendedGeometricCuts F →
        ∃ i : FiveSector,
          Q.projectedVertex (R.spanningCompletion.parents.parent e.val) -
            Q.projectedVertex e.val ∈ closedFiveSector t i ∧
          R.CurvedSubtreeInSector (t := t) i e := by
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
  refine fun e member => ?_
  exact R.val.exists_subtree_sector_of_component_cover R.property
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered)
    (M.exists_cut_component_sector F covered positive small)
    (M.radialMesh_curvature_covered T height) e member

end Unfoldings.ConvexRoof.SectorForest
