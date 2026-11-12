module

public import Unfoldings.Cap.OuterClosedCircleContact
public import Unfoldings.Cap.OuterClosedSectionAlternative
public import Unfoldings.Cap.ClosedOuterSectionComponentBank
public import Unfoldings.Cap.ClosedSectionSharedBankMargins

/-! Weak outer-circle contacts retain equality of both developed and physical endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem weak_closed_sections_outer_banks_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small lower a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (footprint : Q.footprint = K.clipFootprint Z)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (slice : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (other_slice : T.ClosedBankCircleSection other.value other.center cutoff radius)
    (first_pinches : S.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (last_pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small j).place
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)
    (first_outer : Set.EqOn S.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im)
    {p : Plane}
    (first : p ∈ weakCircleUpperCap (B.sectorFrame i)
      (D.projectedMap Q (K.projectedVertex origin)) radius
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last : p ∈ weakCircleLowerCap (B.sectorFrame j)
      (D.projectedMap Q (K.projectedVertex origin)) radius
      (other.value (T.lower.point other_slice.lowerHeight) - other.center).im) :
    p = data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight)) ∧
      (fiveSectorFrame t positive small i).place.symm (S.upper.point slice.upperHeight) =
        (fiveSectorFrame t positive small j).place.symm
          (T.lower.point other_slice.lowerHeight) := by
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  rcases M.outer_closed_section_endpoints_eq_or_common_component F covered positive small
    lower R D
    leaf_coherent data other slice other_slice shared first_outer last_outer radius_positive
    far deep
    with common | ⟨c, member, other_member, unattached⟩
  · let actual := data.outputFrame.symm (data.value (S.upper.point slice.upperHeight))
    have first_height : slice.upperHeight ∈ Set.Ioo 0 cutoff := by
      simpa only [S.upper.point_height] using data.closed_circle_height_mem_Ioo
        radius_positive far slice.upper_closed slice.upper_radius
    have margins := B.closed_section_shared_bank_margins i j true shared positive_margin face_bounds
      data slice radius_positive small_error room
      (first_outer ⟨first_height.1.le, first_height.2.le⟩)
    have first_centered : B.sectorFrame i (actual - D.projectedMap Q (K.projectedVertex origin)) =
        data.value (S.upper.point slice.upperHeight) - data.center := by
      change data.outputFrame (actual - D.projectedMap Q (K.projectedVertex origin)) = _
      rw [map_sub, ← data.center_eq_outputFrame]
      exact congrArg (fun z => z - data.center) (data.outputFrame.apply_symm_apply _)
    have last_centered : B.sectorFrame j (actual - D.projectedMap Q (K.projectedVertex origin)) =
        other.value (T.lower.point other_slice.lowerHeight) - other.center := by
      change other.outputFrame (actual - D.projectedMap Q (K.projectedVertex origin)) = _
      dsimp only [actual]
      rw [common.2, map_sub, LinearIsometryEquiv.apply_symm_apply, ← other.center_eq_outputFrame]
    have size : ‖actual - D.projectedMap Q (K.projectedVertex origin)‖ ≤ radius := by
      rw [data.outputFrame_symm_source_distance]
      exact slice.upper_radius.le
    have equal : p = actual := B.inner_barrier_point_eq_of_norm_le i j
      (D.projectedMap Q (K.projectedVertex origin)) actual p
      (margins i (Or.inl rfl)) (margins j (Or.inr rfl))
      ⟨first.1, first.2.1⟩ ⟨last.1, last.2.1⟩
      (by rw [first_centered]; exact first.2.2.1)
      (by rw [last_centered]; exact last.2.2.1)
      (size.trans_eq first.2.2.2.symm)
    exact ⟨equal, common.2, common.1⟩
  · have first_height : slice.upperHeight ∈ Set.Ioo 0 cutoff := by
      simpa only [S.upper.point_height] using data.closed_circle_height_mem_Ioo
        radius_positive far slice.upper_closed slice.upper_radius
    have last_height : other_slice.lowerHeight ∈ Set.Ioo 0 cutoff := by
      simpa only [T.lower.point_height] using other.closed_circle_height_mem_Ioo
        radius_positive far other_slice.lower_closed other_slice.lower_radius
    have at_root := first_outer ⟨first_height.1.le, first_height.2.le⟩
    have cones := shared_sector_bank_mem_both_cones positive small i j true shared first_height.1
    have first_cone : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point slice.upperHeight) - K.projectedVertex origin ∈ closedFiveSector t i := by
      rw [add_sub_cancel_left, at_root]
      exact cones.1
    have last_cone : K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point slice.upperHeight) - K.projectedVertex origin ∈ closedFiveSector t j := by
      rw [add_sub_cancel_left, at_root]
      exact cones.2
    have boundary : ∀ a, K.projectedVertex origin +
        (fiveSectorFrame t positive small i).place.symm (S.upper.point slice.upperHeight) -
          K.projectedVertex origin ∉ strictFiveSector t a := by
      rw [add_sub_cancel_left, at_root]
      exact (fiveSector_enclosingStrip_bank_not_strict_any positive small i first_height.1.le).2
    have inside := deep (Metric.ball_subset_closedBall
      (data.closed_circle_point_mem_ball small_error slice.upper_closed slice.upper_radius far))
    obtain ⟨_, w, at_seed, coherent_seed, seed_member⟩ :=
      M.fine_coherent_seed_of_boundary_component F covered positive small lower Q D leaf_vertices
        leaf_coherent c member inside boundary
    have seed_first :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone seed_member
    have seed_last :=
      (F.componentTail c).position_inDirectionWedge_of_mem member last_cone seed_member
    obtain ⟨e, child, s, physical, matching⟩ :=
      M.closed_outer_section_bank_on_component F covered lower R outward D B w c unattached
        at_seed footprint i seed_first data slice radius_positive far coherent_seed first_pinches
        true first_outer small_error deep member
    obtain ⟨f, other_child, r, other_physical, other_matching⟩ :=
      M.closed_outer_section_bank_on_component F covered lower R outward D B w c unattached
        at_seed footprint j seed_last other other_slice radius_positive far coherent_seed
        last_pinches false last_outer small_error deep other_member
    simp only [↓reduceIte] at physical matching
    simp only [Bool.false_eq_true, ↓reduceIte] at other_physical other_matching
    have size : ‖R.parentExitPoint (R.completedDevelopment D) e (1 - (s : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
      rw [← matching, data.outputFrame_symm_source_distance]
      exact slice.upper_radius
    have other_size : ‖R.parentEntrancePoint (R.completedDevelopment D) f (1 - (r : ℝ)) -
        D.projectedMap Q (K.projectedVertex origin)‖ = radius := by
      rw [← other_matching, other.outputFrame_symm_source_distance]
      exact other_slice.lower_radius
    have first_inside :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone child
    have last_inside := (F.componentTail c).position_inDirectionWedge_of_mem member last_cone child
    have exit_margins := B.closed_section_shared_bank_margins i j true shared
      positive_margin face_bounds
      data slice radius_positive small_error room at_root
    change ∀ a, a = i ∨ a = j →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).re ∧
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).im at exit_margins
    rw [matching] at exit_margins
    have entrance_margins := B.closed_section_shared_bank_margins j i false shared positive_margin
      face_bounds
      other other_slice radius_positive small_error room
      (last_outer ⟨last_height.1.le, last_height.2.le⟩)
    change ∀ a, a = j ∨ a = i →
      0 < (B.sectorFrame a (other.outputFrame.symm
        (other.value (T.lower.point other_slice.lowerHeight)) -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      0 < (B.sectorFrame a (other.outputFrame.symm
        (other.value (T.lower.point other_slice.lowerHeight)) -
          D.projectedMap Q (K.projectedVertex origin))).im at entrance_margins
    rw [other_matching] at entrance_margins
    have first_centered : data.value (S.upper.point slice.upperHeight) - data.center =
        B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) e
          (1 - (s : ℝ)) - D.projectedMap Q (K.projectedVertex origin)) := by
      have value := congrArg data.outputFrame matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, data.center_eq_outputFrame, map_sub]
      rfl
    have last_centered : other.value (T.lower.point other_slice.lowerHeight) - other.center =
        B.sectorFrame j (R.parentEntrancePoint (R.completedDevelopment D) f
          (1 - (r : ℝ)) - D.projectedMap Q (K.projectedVertex origin)) := by
      have value := congrArg other.outputFrame other_matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, other.center_eq_outputFrame, map_sub]
      rfl
    have contact := M.weak_circle_caps_contact_values_of_component_bank_bounds F covered lower R
      e f c unattached child other_child positive
      small outward footprint i j first_inside last_inside curvature_covered D B budget s r
      (D.projectedMap Q (K.projectedVertex origin)) size.le other_size.le
      (fun a choice => ⟨exit_margins a choice, entrance_margins a choice.symm⟩)
      (by rw [← first_centered]) (by rw [← last_centered]) ⟨first, last⟩
    have physical_equal := M.unattached_component_bank_contact_same_projected_point F covered
      lower R
      e f c unattached child other_child positive
      small outward footprint i first_inside curvature_covered D B budget s r contact.2
    have endpoints := physical.trans (physical_equal.trans other_physical.symm)
    refine ⟨contact.1.trans matching.symm, matching.trans (contact.2.trans other_matching.symm), ?_⟩
    exact add_left_cancel endpoints

end Unfoldings.ConvexCap.SectorForest
