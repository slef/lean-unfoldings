module

public import Unfoldings.Roof.GeometricChainNetwork
public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Cap.CompletedRootPathSupport

/-! A specified geometric component controls fine parent banks starting at any of its cut points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small c)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (w : FineC.Vertex Set.univ) (on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F)
  (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
  (start : Q.projectedVertex w ∈ segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))

include on_cuts component start

/-- The chosen component supplies the sector for every actual fine-path vertex. -/
theorem completed_path_positions :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      (R.completedRootPath w).vertex j - origin ∈
        closedFiveSector t data.sector := by
  let P := R.completedRootPath w
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have cover := fun j => (R.completedRootPath_edge_subset on_cuts j).trans
    (M.extendedGeometricCuts_eq_piece_union F).subset
  intro j
  obtain ⟨piece, member⟩ := Set.mem_iUnion.mp
    ((M.extendedGeometricCuts_eq_piece_union F).subset
      (R.completedRootPath_vertex_mem on_cuts j))
  have same := P.labels_eq_of_segment_cover (M.cutPieceFirst F) (M.cutPieceLast F)
    (M.cutPieceLabel F covered) (M.cutPiece_labels_compatible F covered)
    cover anchor start j piece member
  exact (data.cut_piece_geometry piece (same.trans component)).2 _ member

/-- This works even when the fine starting vertex lies inside an old geometric edge. -/
theorem completed_parent_directions (outward : R.Outward) :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
        Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t data.sector := by
  let P := R.completedRootPath w
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have directions := P.directions_of_labeled_segment_cover (origin)
    (fiveSectorFirst t data.sector) (fiveSectorLast t data.sector)
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (R.completedRootPath_outward outward on_cuts) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered)
    (fun j => (R.completedRootPath_edge_subset on_cuts j).trans
      (M.extendedGeometricCuts_eq_piece_union F).subset)
    anchor start (fun piece same => (data.cut_piece_geometry piece (same.trans component)).1)
  intro j
  have direction := directions j
  change Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val + 1] w) -
    Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val] w) ∈
      closedFiveSector t data.sector at direction
  rw [Function.iterate_succ_apply'] at direction
  exact direction

theorem completed_curved_subtree_sectors (outward : R.Outward)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F) :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.CurvedSubtreeInSector (t := t) data.sector (R.completedBankChain w j) := by
  let P := R.completedRootPath w
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have cover := fun j => (R.completedRootPath_edge_subset on_cuts j).trans
    (M.extendedGeometricCuts_eq_piece_union F).subset
  intro j
  obtain ⟨piece, member⟩ := Set.mem_iUnion.mp
    ((M.extendedGeometricCuts_eq_piece_union F).subset
      (R.completedRootPath_vertex_mem on_cuts j.castSucc))
  have same := P.labels_eq_of_segment_cover (M.cutPieceFirst F) (M.cutPieceLast F)
    (M.cutPieceLabel F covered) (M.cutPiece_labels_compatible F covered)
    cover anchor start j.castSucc piece member
  intro child ancestor curved
  exact R.nonzero_descendant_direction_of_component_cover outward
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered)
    (M.extendedGeometricCuts_eq_piece_union F) (M.cutPiece_outward F positive small)
    (M.cutPiece_labels_compatible F covered) curvature_covered (R.completedBankChain w j)
    child ancestor curved piece member (fiveSectorFirst t data.sector)
    (fiveSectorLast t data.sector)
    (fun k equal => (data.cut_piece_geometry k ((equal.trans same).trans component)).1)

end Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector
