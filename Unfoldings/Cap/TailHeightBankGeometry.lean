module

public import Unfoldings.Cap.GeometricComponentBanks
public import Unfoldings.Cap.LeafCompletedTailTracking

/-! Retargeted actual fine banks retain the specified geometric tail's sector. -/

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

/-- The same sector controls the fine path from an arbitrary intermediate
tail vertex, even when refinement introduced it inside an old geometric edge. -/
theorem completed_bank_geometry_from_height
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    {a : ℝ} (after_leaf : leaf.point.re + leaf.point.im ≤ a)
    (before_end : a < M.geometricTailEndHeight F covered positive small lower i leaf.val)
    (same_start : (fiveSectorFrame t positive small i).place
      (Q.projectedVertex w - K.projectedVertex origin) = leaf.tailGraph.graph.point a)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F) :
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      (R.completedRootPath w).vertex j - K.projectedVertex origin ∈ closedFiveSector t i) ∧
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
        Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j) := by
  let data : M.GeometricComponentSector F covered positive small lower
      (M.geometricComponent F covered leaf.val) :=
    ⟨i, leaf.component_positions, leaf.component_directions⟩
  obtain ⟨anchor, component, start⟩ :=
    leaf.tailGraph.labeled_piece_of_point after_leaf before_end same_start.symm
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset (Set.mem_iUnion.mpr ⟨anchor, start⟩)
  exact ⟨data.completed_path_positions R w on_cuts anchor component start,
    data.completed_parent_directions R w on_cuts anchor component start outward,
    data.completed_curved_subtree_sectors R w on_cuts anchor component start outward
      curvature_covered⟩

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
