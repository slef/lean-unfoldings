module

public import Unfoldings.Roof.SectorBoundaryComponents
public import Unfoldings.Roof.GeometricComponentBanks
public import Unfoldings.Geometry.RadialTailComponentRays
public import Unfoldings.Geometry.ChainHeightCover

/-! Actual completed fine paths cover each unattached radial component up to its outer tip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (w : FineC.Vertex Set.univ) (c : F.Component)
  (unattached : ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)
  (member : Q.projectedVertex w ∈ (F.componentTail c).carrier)

include unattached member

theorem unattached_component_completed_path_positions :
    ∀ j : Fin (R.spanningCompletion.parents.distanceToRoot w + 1),
      (R.completedRootPath w).vertex j ∈ (F.componentTail c).carrier := by
  let P := R.completedRootPath w
  let := F.finite
  let := RadialTailFamily.finiteComponent F.tail
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩
  have cover := fun j => (R.completedRootPath_edge_subset on_cuts j).trans
    (M.extendedGeometricCuts_eq_piece_union F).subset
  intro j
  obtain ⟨piece, inside⟩ := Set.mem_iUnion.mp
    ((M.extendedGeometricCuts_eq_piece_union F).subset (R.completedRootPath_vertex_mem on_cuts j))
  have label := P.labels_eq_of_segment_cover (M.cutPieceFirst F) (M.cutPieceLast F)
    (M.cutPieceLabel F covered) (M.cutPiece_labels_compatible F covered) cover
    (Sum.inr c) member j piece inside
  cases piece with
  | inl e => exact (unattached e label).elim
  | inr d =>
    change d = c at label
    subst d
    exact inside

theorem unattached_component_completed_path_end (footprint : Q.footprint = outerDomain) :
    (R.completedRootPath w).vertex (Fin.last _) = (F.componentTail c).tip := by
  have positions := M.unattached_component_completed_path_positions F covered R w c
    unattached member
  have root_boundary : FineC.IsBoundaryVertex Set.univ (R.spanningCompletion.parents.root w) :=
    (Set.ext_iff.mp R.spanningCompletion.roots_eq _).mp (R.spanningCompletion.parents.root_mem w)
  have endpoint : (R.completedRootPath w).vertex (Fin.last _) =
      Q.projectedVertex (R.spanningCompletion.parents.root w) := by
    change Q.projectedVertex (R.spanningCompletion.parents.parent^[
      R.spanningCompletion.parents.distanceToRoot w] w) = _
    rw [R.spanningCompletion.parents.iterate_distanceToRoot_eq_root]
  have boundary : (R.completedRootPath w).vertex (Fin.last _) ∈ frontier (outerDomain) := by
    have member := (Q.projectedVertex_mem_frontier_iff _).mpr root_boundary
    exact endpoint.symm ▸ (congrArg frontier footprint).subset member
  exact (F.componentTail c).eq_tip_of_mem_frontier (F.convex)
    (F.encloses (interior_subset F.origin)) (positions _) boundary

/-- The point is located on an actual whole fine parent edge. Only physical
height bounds along the chosen sector frame are supplied. -/
theorem unattached_component_point_on_completed_path
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i : FiveSector)
    (inside : Q.projectedVertex w - origin ∈ closedFiveSector t i)
    {x : Plane} (point : x ∈ (F.componentTail c).carrier)
    (start : ((fiveSectorFrame t positive small i).place
        (Q.projectedVertex w - origin)).re +
        ((fiveSectorFrame t positive small i).place
          (Q.projectedVertex w - origin)).im ≤
      ((fiveSectorFrame t positive small i).place (x - origin)).re +
        ((fiveSectorFrame t positive small i).place (x - origin)).im)
    (finish : ((fiveSectorFrame t positive small i).place (x - origin)).re +
        ((fiveSectorFrame t positive small i).place (x - origin)).im <
      ((fiveSectorFrame t positive small i).place
        ((F.componentTail c).tip - origin)).re +
        ((fiveSectorFrame t positive small i).place
          ((F.componentTail c).tip - origin)).im) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      x = (R.completedRootPath w).point j s := by
  let P := R.completedRootPath w
  let frame := (fiveSectorFrame t positive small i).place
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.toLinearMap
  let data := M.radialComponentSector positive small F covered c unattached member i inside
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F := by
    rw [M.extendedGeometricCuts_eq_piece_union F]
    exact Set.mem_iUnion.mpr ⟨Sum.inr c, member⟩
  have directions := data.completed_parent_directions R w on_cuts (Sum.inr c) rfl member outward
  have steps (j : Fin (R.spanningCompletion.parents.distanceToRoot w)) : 0 < height (P.edge j) := by
    have quadrant := (fiveSectorFrame t positive small i).quadrant_self (directions j)
      (R.completed_parent_direction_ne_zero (R.completedBankChain w j).val
        (R.completedBankChain w j).property)
    have edge : P.edge j =
        Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w j).val) -
          Q.projectedVertex (R.completedBankChain w j).val := by
      change Q.projectedVertex (R.spanningCompletion.parents.parent^[j.val + 1] w) - _ = _
      rw [Function.iterate_succ_apply']
      rfl
    change 0 < (frame (P.edge j)).re + (frame (P.edge j)).im
    rw [edge]
    exact add_pos quadrant.1 quadrant.2
  have path_end := M.unattached_component_completed_path_end F covered R w c
    unattached member footprint
  have first_height : height (P.vertex 0) ≤ height x := by
    have raw : height (Q.projectedVertex w - origin) ≤
        height (x - origin) := start
    simp only [map_sub] at raw
    exact (sub_le_sub_iff_right _).mp raw
  have last_height : height x < height (P.vertex (Fin.last _)) := by
    rw [path_end]
    have raw : height (x - origin) <
        height ((F.componentTail c).tip - origin) := finish
    simp only [map_sub] at raw
    exact (sub_lt_sub_iff_right _).mp raw
  obtain ⟨j, s, at_height⟩ := P.exists_point_at_linear_height height steps (height x)
    first_height last_height
  have positions := M.unattached_component_completed_path_positions F covered R w c
    unattached member
  have physical : P.point j s ∈ (F.componentTail c).carrier :=
    (convex_segment (F.componentSeed c) (F.componentTail c).tip).segment_subset
      (positions j.castSucc) (positions j.succ) (lineMap_mem_segment ℝ _ _ s.property)
  have tip_inside := (F.componentTail c).position_inDirectionWedge_of_mem member inside
    (F.componentTail c).tip_mem
  have tip_ne : (F.componentTail c).tip - origin ≠ 0 := by
    intro zero
    exact (F.componentTail c).boundary.2 ((sub_eq_zero.mp zero).symm ▸
      F.encloses (interior_subset F.origin))
  have quadrant := (fiveSectorFrame t positive small i).quadrant_self tip_inside tip_ne
  have height_positive : 0 < height ((F.componentTail c).tip - origin) :=
    add_pos quadrant.1 quadrant.2
  exact ⟨j, s, ((F.componentTail c).eq_of_mem_of_linear_height height height_positive
    physical point at_height).symm⟩

end Unfoldings.ConvexRoof.SectorForest
