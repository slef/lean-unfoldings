module

public import Unfoldings.Roof.RadialComponentSeedPath
public import Unfoldings.Cap.CirclePhysicalBankMatching
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCirclePhysicalBounds

/-! Actual circle endpoints on radial components select named fine parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  {positive : 0 < t} {small : t < 1}
  {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
  (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  (w : FineC.Vertex Set.univ) (c : F.Component)
  (unattached : ∀ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    M.cutPieceLabel F covered (Sum.inl e) ≠ c)
  (at_seed : Q.projectedVertex w = F.componentSeed c)
  (footprint : Q.footprint = outerDomain) (i : FiveSector)
  (inside : Q.projectedVertex w - origin ∈ closedFiveSector t i)
  {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)

include outward unattached at_seed footprint inside radius_positive far outside

theorem lower_circle_bank_on_component
    (member : origin + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ∈ (F.componentTail c).carrier)
    (not_tip : origin + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ≠ (F.componentTail c).tip) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      Q.projectedVertex (R.completedBankChain w j).val ∈ (F.componentTail c).carrier ∧
      data.outputFrame.symm (data.value (S.lower.point slice.lowerHeight)) =
        R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) ∧
      ‖R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) -
        D.projectedMap Q (origin)‖ = radius := by
  have seed_member : Q.projectedVertex w ∈ (F.componentTail c).carrier :=
    at_seed.symm ▸ (F.componentTail c).seed_mem
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset
      (Set.mem_iUnion.mpr ⟨Sum.inr c, seed_member⟩)
  let component := M.radialComponentSector positive small F covered c unattached seed_member
    i inside
  have directions := component.completed_parent_directions R w on_cuts (Sum.inr c) rfl
    seed_member outward
  obtain ⟨j, s, physical⟩ := M.unattached_component_point_on_seed_path F covered R w c
    unattached at_seed positive small outward footprint i inside member not_tip
  have regular := data.regular_of_radius_not_vertexRadii outside slice.lower_closed
    slice.lower_radius
  have matching := B.circle_lower_physical_eq_entrance i data radius_positive far slice w on_cuts
    directions j s regular physical
  have child := M.unattached_component_completed_path_positions F covered R w c unattached
    seed_member j.castSucc
  have size : ‖R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w j)
      (1 - (s : ℝ)) - D.projectedMap Q (origin)‖ = radius := by
    rw [← matching, data.outputFrame_symm_source_distance]
    exact slice.lower_radius
  exact ⟨j, s, child, matching, size⟩

theorem upper_circle_bank_on_component
    (member : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ∈ (F.componentTail c).carrier)
    (not_tip : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ≠ (F.componentTail c).tip) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      Q.projectedVertex (R.completedBankChain w j).val ∈ (F.componentTail c).carrier ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) ∧
      ‖R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) -
        D.projectedMap Q (origin)‖ = radius := by
  have seed_member : Q.projectedVertex w ∈ (F.componentTail c).carrier :=
    at_seed.symm ▸ (F.componentTail c).seed_mem
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset
      (Set.mem_iUnion.mpr ⟨Sum.inr c, seed_member⟩)
  let component := M.radialComponentSector positive small F covered c unattached seed_member
    i inside
  have directions := component.completed_parent_directions R w on_cuts (Sum.inr c) rfl
    seed_member outward
  obtain ⟨j, s, physical⟩ := M.unattached_component_point_on_seed_path F covered R w c
    unattached at_seed positive small outward footprint i inside member not_tip
  have regular := data.regular_of_radius_not_vertexRadii outside slice.upper_closed
    slice.upper_radius
  have matching := B.circle_upper_physical_eq_exit i data radius_positive far slice w on_cuts
    directions j s regular physical
  have child := M.unattached_component_completed_path_positions F covered R w c unattached
    seed_member j.castSucc
  have size : ‖R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w j)
      (1 - (s : ℝ)) - D.projectedMap Q (origin)‖ = radius := by
    rw [← matching, data.outputFrame_symm_source_distance]
    exact slice.upper_radius
  exact ⟨j, s, child, matching, size⟩

theorem lower_circle_bank_on_component_in_sweep
    (small_error : ε < 1 / 2)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (member : origin + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ∈ (F.componentTail c).carrier) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      Q.projectedVertex (R.completedBankChain w j).val ∈ (F.componentTail c).carrier ∧
      data.outputFrame.symm (data.value (S.lower.point slice.lowerHeight)) =
        R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) ∧
      ‖R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) -
        D.projectedMap Q (origin)‖ = radius := by
  have in_ball := data.closed_circle_point_mem_ball small_error slice.lower_closed
    slice.lower_radius far
  have in_clip := deep (Metric.ball_subset_closedBall in_ball)
  have not_tip : origin + (fiveSectorFrame t positive small i).place.symm
      (S.lower.point slice.lowerHeight) ≠ (F.componentTail c).tip := by
    intro equal
    exact (F.componentTail c).boundary.2 (equal ▸ in_clip)
  exact M.lower_circle_bank_on_component F covered R outward D B w c unattached at_seed
    footprint i inside data slice radius_positive far outside member not_tip

theorem upper_circle_bank_on_component_in_sweep
    (small_error : ε < 1 / 2)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (member : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ∈ (F.componentTail c).carrier) :
    ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
      Q.projectedVertex (R.completedBankChain w j).val ∈ (F.componentTail c).carrier ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) ∧
      ‖R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w j) (1 - (s : ℝ)) -
        D.projectedMap Q (origin)‖ = radius := by
  have in_ball := data.closed_circle_point_mem_ball small_error slice.upper_closed
    slice.upper_radius far
  have in_clip := deep (Metric.ball_subset_closedBall in_ball)
  have not_tip : origin + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point slice.upperHeight) ≠ (F.componentTail c).tip := by
    intro equal
    exact (F.componentTail c).boundary.2 (equal ▸ in_clip)
  exact M.upper_circle_bank_on_component F covered R outward D B w c unattached at_seed
    footprint i inside data slice radius_positive far outside member not_tip

end Unfoldings.ConvexRoof.SectorForest
