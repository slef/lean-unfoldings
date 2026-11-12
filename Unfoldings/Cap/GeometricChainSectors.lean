module

public import Unfoldings.Cap.GeometricChainNetwork
public import Unfoldings.Cap.GeometricComponentBanks
public import Unfoldings.Cap.GeometricVertexCutPiece
public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Cap.CompletedRootPathSupport

/-! Fine parent directions use the same chosen sector as their actual geometric leaf. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0}

namespace GeometricComponentSector

/-- Retain the physical sector as well as positivity in its larger frame quadrant. -/
theorem chain_edges_in_sector {c : F.Component}
    (data : M.GeometricComponentSector F covered positive small lower c)
    {n : ℕ} (P : PolygonalChain Plane n)
    (cover : ∀ j : Fin n,
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆ M.extendedGeometricCuts F)
    (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
    (start : P.vertex 0 ∈ segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))
    (outward : ∀ j, 0 ≤ inner ℝ (P.vertex j.castSucc - K.projectedVertex origin) (P.edge j)) :
    ∀ j, P.edge j ∈ closedFiveSector t data.sector := by
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  exact P.directions_of_labeled_segment_cover (K.projectedVertex origin)
    (fiveSectorFirst t data.sector) (fiveSectorLast t data.sector)
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered) outward
    (M.cutPiece_outward F positive small) (M.cutPiece_labels_compatible F covered lower)
    (fun j => (cover j).trans (M.extendedGeometricCuts_eq_piece_union F).subset)
    anchor start (fun k same => (data.cut_piece_geometry k (same.trans component)).1)

end GeometricComponentSector

namespace GeometricSectorLeaf

/-- A specified leaf supplies its own fixed sector to every actual completed
parent edge. No independently chosen component sector has to be identified. -/
theorem completed_bank_directions {i : FiveSector}
    (leaf : M.GeometricSectorLeaf F covered positive small lower i)
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val) :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
        Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i := by
  let data : M.GeometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf.val) :=
    ⟨i, leaf.component_positions, leaf.component_directions⟩
  obtain ⟨anchor, component, start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered
    positive small lower leaf.val leaf.property.1
  have fine_start : Q.projectedVertex w ∈
      segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor) := same_start ▸ start
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset (Set.mem_iUnion.mpr ⟨anchor, fine_start⟩)
  exact data.completed_parent_directions R w on_cuts anchor component fine_start outward

/-- Curvature-carrying descendants along the same fine path retain the specified
leaf sector too. The coverage hypothesis concerns actual nonflat mesh vertices. -/
theorem completed_curved_subtree_sectors {i : FiveSector}
    (leaf : M.GeometricSectorLeaf F covered positive small lower i)
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F) :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j) := by
  let data : M.GeometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf.val) :=
    ⟨i, leaf.component_positions, leaf.component_directions⟩
  obtain ⟨anchor, component, start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered
    positive small lower leaf.val leaf.property.1
  have fine_start : Q.projectedVertex w ∈
      segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor) := same_start ▸ start
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset (Set.mem_iUnion.mpr ⟨anchor, fine_start⟩)
  exact data.completed_curved_subtree_sectors R w on_cuts anchor component fine_start outward
    curvature_covered

end GeometricSectorLeaf
end Unfoldings.ConvexCap.SectorForest
