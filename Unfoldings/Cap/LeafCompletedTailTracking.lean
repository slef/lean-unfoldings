module

public import Unfoldings.Cap.CompletedGeometricTailTracking
public import Unfoldings.Cap.GeometricVertexCutPiece
public import Unfoldings.Cap.GeometricTailCutoff
public import Unfoldings.Cap.GeometricTailPieces

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
theorem tailGraph_point_on_completed_path_from_height
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    {a : ℝ} (after_leaf : leaf.point.re + leaf.point.im ≤ a)
    (same_start : (fiveSectorFrame t positive small i).place
      (Q.projectedVertex w - K.projectedVertex origin) = leaf.tailGraph.graph.point a)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {h : ℝ} (member : h ∈ Set.Icc a cutoff) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      leaf.tailGraph.graph.point h = (fiveSectorFrame t positive small i).place
        ((R.completedRootPath w).point j s - K.projectedVertex origin) := by
  let data : M.GeometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf.val) :=
    ⟨i, leaf.component_positions, leaf.component_directions⟩
  have before_end := (member.1.trans member.2).trans_lt (leaf.tail_end_beyond_clip_ball deep)
  obtain ⟨anchor, component, start⟩ :=
    leaf.tailGraph.labeled_piece_of_point after_leaf before_end same_start.symm
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset (Set.mem_iUnion.mpr ⟨anchor, start⟩)
  exact data.tail_point_on_completed_path_from_height R outward w on_cuts anchor component start
    leaf.property.1 rfl leaf.tailGraph a after_leaf same_start (by rw [footprint]; exact deep)
    (leaf.tail_end_beyond_clip_ball deep) member

/-- Retain the original leaf-start interface. -/
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
  apply leaf.tailGraph_point_on_completed_path_from_height R outward w le_rfl _
    footprint deep member
  rw [same_start]
  exact (leaf.tailGraph.graph.point_eq_of_coordinate leaf.point leaf.tailGraph_target).symm

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
