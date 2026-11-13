module

public import Unfoldings.Roof.GeometricComponentBanks
public import Unfoldings.Roof.LeafCompletedTailTracking

/-! Retargeted actual fine banks retain the specified geometric tail's sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small i)

/-- The same sector controls the fine path from an arbitrary intermediate
tail vertex, even when refinement introduced it inside an old geometric edge. -/
theorem completed_bank_geometry_from_height
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (w : FineC.Vertex Set.univ)
    {a : ℝ} (after_leaf : leaf.point.re + leaf.point.im ≤ a)
    (before_end : a < M.geometricTailEndHeight F covered positive small i leaf.val)
    (same_start : (fiveSectorFrame t positive small i).place
      (Q.projectedVertex w - origin) = leaf.tailGraph.graph.point a)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F) :
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      (R.completedRootPath w).vertex j - origin ∈ closedFiveSector t i) ∧
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
        Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j) := by
  let data : M.GeometricComponentSector F covered positive small
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

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
