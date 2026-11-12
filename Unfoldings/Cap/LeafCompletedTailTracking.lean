module

public import Unfoldings.Cap.CompletedGeometricTailTracking
public import Unfoldings.Cap.GeometricVertexCutPiece
public import Unfoldings.Cap.GeometricTailCutoff

/-! Every constructed leaf's tail is tracked by the actual fine outward forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)

/-- One physical start identifies the actual fine path. The containing cut piece,
component label, nonconstant radial tail, and both stopping-height bounds are derived. -/
theorem tailGraph_point_on_completed_path
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    (same_start : Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {h : ℝ} (member : h ∈ Set.Icc (leaf.point.re + leaf.point.im) cutoff) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      leaf.tailGraph.graph.point h = (fiveSectorFrame t positive small i).place
        ((R.completedRootPath w).point j s - K.projectedVertex origin) := by
  let data : M.GeometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf.val) :=
    ⟨i, leaf.component_positions, leaf.component_directions⟩
  obtain ⟨anchor, component, start⟩ := M.geometric_vertex_mem_labeled_cut_piece F covered
    positive small lower leaf.val leaf.property.1
  have fine_start : Q.projectedVertex w ∈
      segment ℝ (M.cutPieceFirst F anchor) (M.cutPieceLast F anchor) := same_start ▸ start
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset (Set.mem_iUnion.mpr ⟨anchor, fine_start⟩)
  exact data.tail_point_on_completed_path R outward w on_cuts anchor component fine_start
    leaf.property.1 rfl leaf.tailGraph same_start (by rw [footprint]; exact deep)
    (leaf.tail_end_beyond_clip_ball deep) member

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
