module

public import Unfoldings.Cap.GeometricComponentNetwork
public import Unfoldings.Geometry.ChainPointCoverLabels
public import Unfoldings.Geometry.HeightNetworkChainTracking

/-! Physical fine cut chains inherit the actual sector network and its positive coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricComponentSector

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small lower c)

/-- Component labels propagate to all fine-edge points, so the actual geometric
network covers the whole chain, independently of its subdivision. -/
theorem chain_points_mem_heightNetwork
    (genuine : F.componentSeed c ≠ (F.componentTail c).tip)
    {n : ℕ} (P : PolygonalChain Plane n)
    (cover : ∀ j : Fin n,
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆ M.extendedGeometricCuts F)
    (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
    (start : P.vertex 0 ∈ segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))
    (j : Fin n) (s : unitInterval) :
    (fiveSectorFrame t positive small data.sector).place (P.point j s - K.projectedVertex origin) ∈
      (M.sectorHeightNetwork F covered positive small lower data.sector).carrier := by
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have whole_cover := fun j => (cover j).trans (M.extendedGeometricCuts_eq_piece_union F).subset
  obtain ⟨k, inside⟩ := Set.mem_iUnion.mp (whole_cover j (lineMap_mem_segment ℝ _ _ s.property))
  have same := P.point_label_eq_of_segment_cover (M.cutPieceFirst F) (M.cutPieceLast F)
    (M.cutPieceLabel F covered) (M.cutPiece_labels_compatible F covered lower)
    whole_cover anchor start j s k inside
  exact data.cut_piece_mem_heightNetwork genuine k (same.trans component) inside

/-- Outward fine edges inherit positive coordinates from the chosen component's
actual coarse directions. No acute-angle hypothesis is imposed on the fine mesh. -/
theorem chain_edges_positive
    {n : ℕ} (P : PolygonalChain Plane n)
    (cover : ∀ j : Fin n,
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆ M.extendedGeometricCuts F)
    (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
    (start : P.vertex 0 ∈ segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))
    (outward : ∀ j, 0 ≤ inner ℝ (P.vertex j.castSucc - K.projectedVertex origin) (P.edge j))
    (genuine : ∀ j, P.edge j ≠ 0) (j : Fin n) :
    0 < ((fiveSectorFrame t positive small data.sector).place (P.edge j)).re ∧
      0 < ((fiveSectorFrame t positive small data.sector).place (P.edge j)).im := by
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have directions := P.directions_of_labeled_segment_cover (K.projectedVertex origin)
    (fiveSectorFirst t data.sector) (fiveSectorLast t data.sector)
    (M.cutPieceFirst F) (M.cutPieceLast F) (M.cutPieceLabel F covered) outward
    (M.cutPiece_outward F positive small) (M.cutPiece_labels_compatible F covered lower)
    (fun j => (cover j).trans (M.extendedGeometricCuts_eq_piece_union F).subset)
    anchor start (fun k same => (data.cut_piece_geometry k (same.trans component)).1)
  exact (fiveSectorFrame t positive small data.sector).quadrant_self (directions j) (genuine j)

end Unfoldings.ConvexCap.SectorForest.GeometricComponentSector
