module

public import Unfoldings.Cap.GeometricChainNetwork
public import Unfoldings.Cap.GeometricTailCoalescence

/-! The actual geometric tail point is on a whole edge of every outward fine cut chain. -/

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

/-- Forward uniqueness transfers an exact geometric tail to any physical outward
chain on the same actual cuts. Coarse/fine edge correspondences are a conclusion. -/
theorem tail_point_on_cut_chain
    (component_genuine : F.componentSeed c ≠ (F.componentTail c).tip)
    {n : ℕ} (P : PolygonalChain Plane n)
    (cover : ∀ j : Fin n,
      segment ℝ (P.vertex j.castSucc) (P.vertex j.succ) ⊆ M.extendedGeometricCuts F)
    (anchor : M.ExtendedCutPiece F) (component : M.cutPieceLabel F covered anchor = c)
    (start : P.vertex 0 ∈ segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor))
    (outward : ∀ j, 0 ≤ inner ℝ (P.vertex j.castSucc - K.projectedVertex origin) (P.edge j))
    (genuine : ∀ j, P.edge j ≠ 0)
    {w : F.GeometricVertex} (H : M.SectorTailGraph F covered positive small lower data.sector w)
    (same_start : P.vertex 0 = F.geometricPosition w) {b : ℝ}
    (fine_finish : b <
      ((fiveSectorFrame t positive small data.sector).place
        (P.vertex (Fin.last n) - K.projectedVertex origin)).re +
      ((fiveSectorFrame t positive small data.sector).place
        (P.vertex (Fin.last n) - K.projectedVertex origin)).im)
    (tail_finish : b < M.geometricTailEndHeight F covered positive small lower data.sector w)
    {h : ℝ} (member : h ∈ Set.Icc
      (M.geometricTailStartHeight F covered positive small lower data.sector w) b) :
    ∃ j : Fin n, ∃ s : unitInterval, H.graph.point h =
      (fiveSectorFrame t positive small data.sector).place
        (P.point j s - K.projectedVertex origin) := by
  let frame := (fiveSectorFrame t positive small data.sector).place
  let A := centeredPlaneFrame (K.projectedVertex origin) frame
  have linear (v : Plane) : A.toAffineMap.linear v = frame v := rfl
  have height : (A (P.vertex 0)).re + (A (P.vertex 0)).im =
      M.geometricTailStartHeight F covered positive small lower data.sector w := by
    rw [same_start, centeredPlaneFrame_apply]
    rfl
  have initial : H.graph.coordinate ((A (P.vertex 0)).re + (A (P.vertex 0)).im) =
      (A (P.vertex 0)).re := by
    rw [same_start, centeredPlaneFrame_apply]
    exact H.vertices 0
  have steps := data.chain_edges_positive P cover anchor component start outward genuine
  have chain_cover (j : Fin n) (s : unitInterval) : A (P.point j s) ∈
      (M.sectorHeightNetwork F covered positive small lower data.sector).carrier := by
    rw [centeredPlaneFrame_apply]
    exact data.chain_points_mem_heightNetwork component_genuine P cover anchor component start j s
  have finish : b < (A (P.vertex (Fin.last n))).re + (A (P.vertex (Fin.last n))).im := by
    rw [centeredPlaneFrame_apply]
    exact fine_finish
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  obtain ⟨j, s, value⟩ :=
    HeightSegmentNetwork.heightGraph_point_on_affine_covered_chain
      (M.sectorHeightNetwork F covered positive small lower data.sector) A.toAffineMap P
      (fun j => by rw [linear]; exact ⟨(steps j).1.le, (steps j).2.le⟩)
      (fun j => by rw [linear]; exact add_pos (steps j).1 (steps j).2)
      chain_cover H.graph (fun h inside => H.covered h (height ▸ inside.1)
        (inside.2.trans_lt tail_finish)) initial
      finish (height ▸ member)
  exact ⟨j, s, value.trans (centeredPlaneFrame_apply _ _ _)⟩

end Unfoldings.ConvexCap.SectorForest.GeometricComponentSector
