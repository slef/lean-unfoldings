module

public import Unfoldings.Cap.SectorBoundaryComponents
public import Unfoldings.Cap.GeometricComponentBanks

/-! An actual boundary cut path can use either neighboring sector's bank comparison. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  (positive : 0 < t) (small : t < 1)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)

include positive small covered lower

/-- Sector membership is derived for all actual fine parent directions and
curved descendants. The caller chooses either sector containing the boundary
ray; no assignment of the whole auxiliary triangulation to that sector is needed. -/
theorem sector_boundary_completed_bank_geometry
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (w : FineC.Vertex Set.univ) (c : F.Component)
    (member : Q.projectedVertex w ∈ (F.componentTail c).carrier)
    (boundary : ∀ j, Q.projectedVertex w - K.projectedVertex origin ∉ strictFiveSector t j)
    (i : FiveSector)
    (inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i) :
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      (R.completedRootPath w).vertex j - K.projectedVertex origin ∈ closedFiveSector t i) ∧
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
        Q.projectedVertex (R.completedBankChain w j).val ∈ closedFiveSector t i) ∧
    (∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.CurvedSubtreeInSector (t := t) i (R.completedBankChain w j)) := by
  let data := M.radialComponentSector positive small F covered lower c
    (M.sector_boundary_component_unattached positive small F covered member boundary)
    member i inside
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩
  exact ⟨data.completed_path_positions R w on_cuts (Sum.inr c) rfl member,
    data.completed_parent_directions R w on_cuts (Sum.inr c) rfl member outward,
    data.completed_curved_subtree_sectors R w on_cuts (Sum.inr c) rfl member outward
      curvature_covered⟩

end Unfoldings.ConvexCap.SectorForest
