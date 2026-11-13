module

public import Unfoldings.Cap.RadialComponentCommonChain
public import Unfoldings.Roof.RadialComponentFineAncestry
public import Unfoldings.Cap.CrossFrameInnerTerminalSeparation
public import Unfoldings.Geometry.RadialTailHeightOrder

/-! Actual fine edges on one pure radial component belong to one common parent chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v u₁ v₁



namespace SectorForest

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (e f : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots})
  (c : F.Component)
  (unattached : ∀ a : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl a) ≠ c)
  (first : Q.projectedVertex e.val ∈ (F.componentTail c).carrier)
  (last : Q.projectedVertex f.val ∈ (F.componentTail c).carrier)

include unattached first last

/-- Neither fine child can be the outer tip, since completed roots are exactly
the outer boundary vertices. Physical height order consequently gives ancestry. -/
theorem unattached_component_nonroot_vertices_comparable
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i : FiveSector)
    (inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i) :
    R.spanningCompletion.parents.Ancestor e.val f.val ∨
      R.spanningCompletion.parents.Ancestor f.val e.val := by
  let frame := (fiveSectorFrame t positive small i).place
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.toLinearMap
  have other_inside := (F.componentTail c).position_inDirectionWedge_of_mem first inside last
  have tip_inside := (F.componentTail c).position_inDirectionWedge_of_mem first inside
    (F.componentTail c).tip_mem
  have tip_ne : (F.componentTail c).tip - origin ≠ 0 := by
    intro zero
    exact (F.componentTail c).boundary.2 ((sub_eq_zero.mp zero).symm ▸
      F.encloses (interior_subset F.origin))
  have quadrant := (fiveSectorFrame t positive small i).quadrant_self tip_inside tip_ne
  have height_positive : 0 < height ((F.componentTail c).tip - origin) :=
    add_pos quadrant.1 quadrant.2
  have different (a : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}) :
      Q.projectedVertex a.val ≠ (F.componentTail c).tip := by
    intro equal
    have boundary : Q.projectedVertex a.val ∈ frontier Q.footprint := by
      rw [footprint, equal]
      exact (F.componentTail c).boundary
    exact a.property ((Set.ext_iff.mp R.spanningCompletion.roots_eq _).mpr
      ((Q.projectedVertex_mem_frontier_iff a.val).mp boundary))
  have first_end := (F.componentTail c).linear_height_lt_tip_of_mem_ne height height_positive
    first (different e)
  have last_end := (F.componentTail c).linear_height_lt_tip_of_mem_ne height height_positive
    last (different f)
  rcases le_total (height (Q.projectedVertex e.val - origin))
    (height (Q.projectedVertex f.val - origin)) with before | after
  · exact Or.inl (M.unattached_component_vertex_ancestor F covered R e.val f.val c
      unattached first positive small outward footprint i inside last before last_end)
  · exact Or.inr (M.unattached_component_vertex_ancestor F covered R f.val e.val c
      unattached last positive small outward footprint i other_inside first after first_end)

/-- Return actual edge names at actual indices of a single completed path. -/
theorem unattached_component_exists_common_bank_chain
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i : FiveSector)
    (inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i) :
    ∃ w : FineC.Vertex Set.univ, ∃ j k : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.completedBankChain w j = e ∧ R.completedBankChain w k = f ∧
      Q.projectedVertex w ∈ (F.componentTail c).carrier := by
  rcases M.unattached_component_nonroot_vertices_comparable F covered R e f c
    unattached first last positive small outward footprint i inside with before | after
  · obtain ⟨j, k, left, right⟩ := R.exists_common_completed_bank_chain_of_ancestor e f before
    exact ⟨e.val, j, k, left, right, first⟩
  · obtain ⟨k, j, right, left⟩ := R.exists_common_completed_bank_chain_of_ancestor f e after
    exact ⟨f.val, j, k, left, right, last⟩

theorem unattached_component_common_bank_chain_geometry
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t l)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F) :
    ∃ w : FineC.Vertex Set.univ, ∃ j k : Fin (R.spanningCompletion.parents.distanceToRoot w),
      R.completedBankChain w j = e ∧ R.completedBankChain w k = f ∧
      ∀ a, a = i ∨ a = l →
        (∀ r : Fin (R.spanningCompletion.parents.distanceToRoot w),
          R.CurvedSubtreeInSector (t := t) a (R.completedBankChain w r)) ∧
        (∀ r : Fin (R.spanningCompletion.parents.distanceToRoot w),
          Q.projectedVertex (R.spanningCompletion.parents.parent (R.completedBankChain w r).val) -
            Q.projectedVertex (R.completedBankChain w r).val ∈ closedFiveSector t a) := by
  obtain ⟨w, j, k, left, right, start⟩ := M.unattached_component_exists_common_bank_chain F
    covered R e f c unattached first last positive small outward footprint i first_inside
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset
      (Set.mem_iUnion.mpr ⟨Sum.inr c, start⟩)
  refine ⟨w, j, k, left, right, ?_⟩
  intro a choice
  have ray : Q.projectedVertex e.val - origin ∈ closedFiveSector t a := by
    rcases choice with rfl | rfl
    · exact first_inside
    · exact last_inside
  have inside := (F.componentTail c).position_inDirectionWedge_of_mem first ray start
  let data := M.radialComponentSector positive small F covered c unattached start a inside
  exact ⟨data.completed_curved_subtree_sectors R w on_cuts (Sum.inr c) rfl start outward
      curvature_covered,
    data.completed_parent_directions R w on_cuts (Sum.inr c) rfl start outward⟩

/-- The comparison uses actual edge names. The common path, its two sector
assignments, every parent direction, and every curved subtree are derived. -/
theorem unattached_component_bank_points_cross_frame_alternative
    (positive : 0 < t) (small : t < 1) (outward : R.Outward)
    (footprint : Q.footprint = outerDomain) (i l : FiveSector)
    (first_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t i)
    (last_inside : Q.projectedVertex e.val - origin ∈ closedFiveSector t l)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (s r : unitInterval) (center : Plane) :
    (B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).re ≤
        (B.sectorFrame i
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).re ∨
      (B.sectorFrame l
          (R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) - center)).im ≤
        (B.sectorFrame l
          (R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) - center)).im := by
  obtain ⟨w, j, k, left, right, geometry⟩ := M.unattached_component_common_bank_chain_geometry F
    covered R e f c unattached first last positive small outward footprint i l
    first_inside last_inside curvature_covered
  have comparison := B.chain_points_cross_frame_alternative i l (R.completedBankChain w)
    (R.completedBankChain_parent w) (geometry i (Or.inl rfl)).1
    (geometry l (Or.inr rfl)).1 (geometry i (Or.inl rfl)).2
    (geometry l (Or.inr rfl)).2 budget j k s r center
  rwa [left, right] at comparison

end SectorForest
end Unfoldings.ConvexRoof
