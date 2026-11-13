module

public import Unfoldings.Roof.RadialComponentCirclePhysicalBanks
public import Unfoldings.Cap.RadialClosedCircleSections
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.ClosedParentPathBankMatching
public import Unfoldings.Cap.CoherentParentBankPoints
public import Unfoldings.Cap.CoherentPhysicalTraceContact
public import Unfoldings.Geometry.RadialTailSeedHeight
public import Unfoldings.Cap.EnclosingBankSegments

/-! Named component circle banks retain their exact physical surface coordinates. -/

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
  (slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (coherent : D.ProjectedCoherentAt Q (Q.projectedVertex w))
  (pinches : S.ApproachedPinchesIn
    (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
        M.extendedGeometricCuts F} =>
      (fiveSectorFrame t positive small i).place
        (Q.projectedVertex v.val - origin))) 0 cutoff)

include outward unattached at_seed footprint inside coherent pinches radius_positive far

/-- An actual outer bank retains its component-bank parameter at every closed circle section. -/
theorem closed_outer_section_bank_on_component (upper : Bool)
    (outer : Set.EqOn (if upper then S.upper else S.lower).point
      (if upper then (fiveSectorFrame t positive small i).enclosingStrip.upper
        else (fiveSectorFrame t positive small i).enclosingStrip.lower).point (Set.Icc 0 cutoff))
    (small_error : ε < 1 / 2)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (member : origin + (fiveSectorFrame t positive small i).place.symm
      (if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight) ∈
        (F.componentTail c).carrier) :
    let z := if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight
    ∃ e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots},
      Q.projectedVertex e.val ∈ (F.componentTail c).carrier ∧ ∃ s : unitInterval,
        origin + (fiveSectorFrame t positive small i).place.symm z =
          AffineMap.lineMap (Q.projectedVertex e.val)
            (Q.projectedVertex (R.spanningCompletion.parents.parent e.val)) (s : ℝ) ∧
        data.outputFrame.symm (data.value z) =
          (if upper then R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ))
            else R.parentEntrancePoint (R.completedDevelopment D) e (1 - (s : ℝ))) := by
  let frame := fiveSectorFrame t positive small i
  let H := if upper then S.upper else S.lower
  let J := if upper then frame.enclosingStrip.upper else frame.enclosingStrip.lower
  let h := if upper then slice.upperHeight else slice.lowerHeight
  let x := origin + frame.place.symm (H.point h)
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp frame.place.toLinearMap
  let a := height (Q.projectedVertex w - origin)
  have point_eq : H.point h =
      (if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight) := by
    cases upper <;> rfl
  have actual_member : x ∈ (F.componentTail c).carrier := by
    simpa only [x, point_eq] using member
  have closed : H.point h ∈ closure data.strictDomain := by
    cases upper
    · exact slice.lower_closed
    · exact slice.upper_closed
  have size : ‖data.value (H.point h) - data.center‖ = radius := by
    cases upper
    · exact slice.lower_radius
    · exact slice.upper_radius
  have bounds : h ∈ Set.Ioo 0 cutoff := by
    simpa only [H.point_height] using data.closed_circle_height_mem_Ioo
      radius_positive far closed size
  have target_on_bank : frame.place (x - origin) = J.point h := by
    rw [show frame.place (x - origin) = H.point h by
      dsimp only [x]; rw [add_sub_cancel_left, frame.place.apply_symm_apply]]
    exact outer ⟨bounds.1.le, bounds.2.le⟩
  have target_height : height (x - origin) = h := by
    change (frame.place (x - origin)).re +
      (frame.place (x - origin)).im = h
    rw [target_on_bank, J.point_height]
  have seed_member : Q.projectedVertex w ∈ (F.componentTail c).carrier :=
    at_seed.symm ▸ (F.componentTail c).seed_mem
  obtain ⟨r, positive_scale, seed_scale⟩ :=
    (F.componentTail c).exists_pos_smul_sub_eq_of_members actual_member seed_member
  have seed_on_bank : 0 < a ∧ frame.place (Q.projectedVertex w - origin) =
      J.point a := by
    cases upper
    · exact frame.enclosingStrip_lower_point_of_pos_scale positive_scale bounds.1
        target_on_bank seed_scale
    · exact frame.enclosingStrip_upper_point_of_pos_scale positive_scale bounds.1
        target_on_bank seed_scale
  obtain ⟨r, rpositive, at_tip⟩ := (F.componentTail c).exists_tip_scale_of_mem actual_member
  have tip_height : 0 < height ((F.componentTail c).tip - origin) := by
    rw [← at_tip, add_sub_cancel_left, map_smul, target_height]
    exact mul_pos rpositive bounds.1
  have before : a ≤ h := by
    have ordered := (F.componentTail c).linear_height_seed_le_of_mem height
      tip_height.le actual_member
    change height (F.componentSeed c - origin) ≤
      height (x - origin) at ordered
    rwa [← at_seed, target_height] at ordered
  have seed_physical : origin + frame.place.symm (J.point a) =
      Q.projectedVertex w := by
    rw [← seed_on_bank.2, frame.place.symm_apply_apply]
    abel
  have on_cuts : Q.projectedVertex w ∈ M.extendedGeometricCuts F :=
    (M.extendedGeometricCuts_eq_piece_union F).symm.subset
      (Set.mem_iUnion.mpr ⟨Sum.inr c, seed_member⟩)
  let component := M.radialComponentSector positive small F covered c unattached seed_member
    i inside
  have directions := component.completed_parent_directions R w on_cuts (Sum.inr c) rfl
    seed_member outward
  have region := deep (Metric.ball_subset_closedBall
    (data.closed_circle_point_mem_ball small_error closed size far))
  have not_tip : x ≠ (F.componentTail c).tip :=
    fun equal => (F.componentTail c).boundary.2 (equal ▸ region)
  have finish : h < height ((F.componentTail c).tip - origin) := by
    rw [← target_height]
    exact (F.componentTail c).linear_height_lt_tip_of_mem_ne height tip_height actual_member not_tip
  by_cases equal : a = h
  · have at_seed_point : x = Q.projectedVertex w := by
      rw [equal] at seed_physical
      dsimp only [x]
      rw [outer ⟨bounds.1.le, bounds.2.le⟩]
      exact seed_physical
    have nonroot : w ∉ R.spanningCompletion.parents.roots := by
      intro root
      have boundary := (Set.ext_iff.mp R.spanningCompletion.roots_eq w).mp root
      have seed_inside : Q.projectedVertex w ∈ interior Q.footprint := by
        rw [footprint, ← at_seed_point]
        exact region
      exact ((Q.projectedVertex_mem_interior_iff w).mp seed_inside) boundary
    let e : {v : FineC.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots} := ⟨w, nonroot⟩
    have physical_coherent : D.ProjectedCoherentAt Q
        (origin + (fiveSectorFrame t positive small i).place.symm
          (H.point h)) := by
      change D.ProjectedCoherentAt Q x
      rw [at_seed_point]
      exact coherent
    have value := data.physical_value_of_closed_coherent closed physical_coherent
    have actual_value : data.outputFrame.symm (data.value (H.point h)) =
        D.projectedMap Q (Q.projectedVertex w) := by
      rw [value, data.outputFrame.symm_apply_apply]
      exact congrArg (D.projectedMap Q) at_seed_point
    have banks := R.parent_bank_child_eq_of_coherent D e coherent
    refine ⟨e, seed_member, 0, ?_, ?_⟩
    · change origin + frame.place.symm
        (if upper then S.upper.point slice.upperHeight else S.lower.point slice.lowerHeight) =
          AffineMap.lineMap (Q.projectedVertex w)
            (Q.projectedVertex (R.spanningCompletion.parents.parent w)) (0 : ℝ)
      rw [← point_eq, AffineMap.lineMap_apply_zero]
      exact at_seed_point
    · rw [← point_eq, actual_value]
      simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
      cases upper
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact banks.1.symm
      · simp only [↓reduceIte]
        exact banks.2.symm
  have strict : a < h := lt_of_le_of_ne before equal
  have tracked (k : ℝ) (interval : k ∈ Set.Ioo a h) :
      ∃ j : Fin (R.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        origin + frame.place.symm (H.point k) =
          (R.completedRootPath w).point j s := by
    have k_bounds : k ∈ Set.Icc 0 cutoff :=
      ⟨seed_on_bank.1.le.trans interval.1.le, interval.2.le.trans bounds.2.le⟩
    have on_segment : origin + frame.place.symm (J.point k) ∈
        segment ℝ (Q.projectedVertex w) x := by
      have first := seed_physical
      have last : origin + frame.place.symm (J.point h) = x := by
        dsimp only [x]
        rw [outer ⟨bounds.1.le, bounds.2.le⟩]
      have between : origin + frame.place.symm (J.point k) ∈ segment ℝ
          (origin + frame.place.symm (J.point a))
          (origin + frame.place.symm (J.point h)) := by
        cases upper
        · exact frame.enclosingStrip_lower_physical_mem_segment
            (origin) seed_on_bank.1.le ⟨interval.1.le, interval.2.le⟩
        · exact frame.enclosingStrip_upper_physical_mem_segment
            (origin) seed_on_bank.1.le ⟨interval.1.le, interval.2.le⟩
      rwa [first, last] at between
    have k_member : origin + frame.place.symm (H.point k) ∈
        (F.componentTail c).carrier := by
      rw [outer k_bounds]
      exact (convex_segment (F.componentSeed c) (F.componentTail c).tip).segment_subset
        seed_member actual_member on_segment
    have k_height : height (origin + frame.place.symm (H.point k) -
        origin) = k := by
      change (frame.place (_ - _)).re + (frame.place (_ - _)).im = k
      rw [add_sub_cancel_left, frame.place.apply_symm_apply, H.point_height]
    exact M.unattached_component_point_on_completed_path F covered R w c unattached
      seed_member positive small outward footprint i inside k_member
      (by change a ≤ height (_ - _); rw [k_height]; exact interval.1.le)
      (by change height (_ - _) < height (_ - _); rw [k_height]; exact interval.2.trans finish)
  have closed_prior (k : ℝ) (interval : k ∈ Set.Ioo a h) :
      H.point k ∈ closure data.strictDomain := by
    cases upper
    · exact data.lower_bank_closed_before closed
        (by rw [H.point_height]; exact ⟨seed_on_bank.1.le.trans interval.1.le, interval.2.le⟩)
    · exact data.upper_bank_closed_before closed
        (by rw [H.point_height]; exact ⟨seed_on_bank.1.le.trans interval.1.le, interval.2.le⟩)
  have child (j : Fin (R.spanningCompletion.parents.distanceToRoot w)) :
      Q.projectedVertex (R.completedBankChain w j).val ∈ (F.componentTail c).carrier :=
    M.unattached_component_completed_path_positions F covered R w c unattached
      seed_member j.castSucc
  cases upper
  · obtain ⟨j, s, physical, value⟩ := B.lower_matches_completed_path_on_closed_interval i w
      on_cuts directions data pinches seed_on_bank.1.le strict bounds.2.le closed_prior tracked
      slice.lowerHeight ⟨strict.le, le_rfl⟩
    refine ⟨R.completedBankChain w j, child j, s,
      physical.trans (R.completedRootPath_point_bankChain w j s), ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [value]
    exact (B.sectorFrame i).symm_apply_apply _
  · obtain ⟨j, s, physical, value⟩ := B.upper_matches_completed_path_on_closed_interval i w
      on_cuts directions data pinches seed_on_bank.1.le strict bounds.2.le closed_prior tracked
      slice.upperHeight ⟨strict.le, le_rfl⟩
    refine ⟨R.completedBankChain w j, child j, s,
      physical.trans (R.completedRootPath_point_bankChain w j s), ?_⟩
    simp only [↓reduceIte]
    rw [value]
    exact (B.sectorFrame i).symm_apply_apply _

end Unfoldings.ConvexRoof.SectorForest
