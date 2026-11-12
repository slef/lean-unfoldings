module

public import Unfoldings.Cap.RadialComponentFinePath
public import Unfoldings.Geometry.RadialTailHeightOrder

/-! The actual fine path from a component seed covers all of its nontip positions. -/

@[expose] public section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (lower : Z < 0)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (w : FineC.Vertex Set.univ) (c : F.Component)
  (unattached : ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)
  (at_seed : Q.projectedVertex w = F.componentSeed c)

include lower unattached at_seed

theorem unattached_component_point_on_seed_path
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = K.clipFootprint Z) (i : FiveSector)
    (inside : Q.projectedVertex w - K.projectedVertex origin ∈ closedFiveSector t i)
    {x : Plane} (member : x ∈ (F.componentTail c).carrier) (not_tip : x ≠ (F.componentTail c).tip) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      x = (R.completedRootPath w).point j s := by
  let frame := (fiveSectorFrame t positive small i).place
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.toLinearMap
  have seed_member : Q.projectedVertex w ∈ (F.componentTail c).carrier :=
    at_seed.symm ▸ (F.componentTail c).seed_mem
  have tip_inside := (F.componentTail c).position_inDirectionWedge_of_mem seed_member inside
    (F.componentTail c).tip_mem
  have tip_ne : (F.componentTail c).tip - K.projectedVertex origin ≠ 0 := by
    intro zero
    exact (F.componentTail c).boundary.2 ((sub_eq_zero.mp zero).symm ▸
      K.original_footprint_in_clip_interior lower (interior_subset F.origin))
  have quadrant := (fiveSectorFrame t positive small i).quadrant_self tip_inside tip_ne
  have height_positive : 0 < height ((F.componentTail c).tip - K.projectedVertex origin) :=
    add_pos quadrant.1 quadrant.2
  obtain ⟨a, bounds, position⟩ := (F.componentTail c).carrier_eq_image.subset member
  change K.projectedVertex origin + a • ((F.componentTail c).tip - K.projectedVertex origin) = x
    at position
  have seed : F.componentSeed c = K.projectedVertex origin +
      (F.componentTail c).start • ((F.componentTail c).tip - K.projectedVertex origin) :=
    (F.componentTail c).seed_eq
  have start : height (Q.projectedVertex w - K.projectedVertex origin) ≤
      height (x - K.projectedVertex origin) := by
    rw [at_seed, seed, ← position, add_sub_cancel_left,
      add_sub_cancel_left, map_smul, map_smul]
    exact mul_le_mul_of_nonneg_right bounds.1 height_positive.le
  have finish := (F.componentTail c).linear_height_lt_tip_of_mem_ne height height_positive
    member not_tip
  exact M.unattached_component_point_on_completed_path F covered lower R w c unattached seed_member
    positive small outward footprint i inside member start finish

end Unfoldings.ConvexCap.SectorForest
