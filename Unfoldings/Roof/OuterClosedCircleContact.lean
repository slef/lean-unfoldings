module

public import Unfoldings.Roof.OuterCircleCaps
public import Unfoldings.Roof.OuterCirclePhysicalAlternative
public import Unfoldings.Roof.RadialComponentCirclePhysicalBanks
public import Unfoldings.Roof.ComponentBankCircleContact
public import Unfoldings.Cap.ClosedStripCircleCaps

/-! Weak outer-circle contacts retain equality of both developed and physical endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outerDomain : Set Plane} (F : K.SkirtTailFamily outerDomain (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem weak_circle_outer_banks_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (footprint : Q.footprint = outerDomain)
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
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_outer : Set.EqOn S.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (origin) cutoff →
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).re ∧
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).im)
    {p : Plane}
    (first : p ∈ weakCircleUpperCap (B.sectorFrame i)
      (D.projectedMap Q (origin)) radius
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last : p ∈ weakCircleLowerCap (B.sectorFrame j)
      (D.projectedMap Q (origin)) radius
      (other.value (T.lower.point other_slice.lowerHeight) - other.center).im) :
    p = data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight)) ∧
      (fiveSectorFrame t positive small i).place.symm (S.upper.point slice.upperHeight) =
        (fiveSectorFrame t positive small j).place.symm
          (T.lower.point other_slice.lowerHeight) := by
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  rcases M.outer_circle_physical_endpoints_eq_or_common_component F covered positive small
     R D
    leaf_coherent data other slice other_slice shared first_outer last_outer radius_positive
    far deep
    with common | ⟨c, member, other_member, unattached⟩
  · let actual := data.outputFrame.symm (data.value (S.upper.point slice.upperHeight))
    have first_height := (data.circle_slice_heights radius_positive far slice).2
    have margins := B.circle_shared_bank_margins i j true shared positive_margin face_bounds
      data slice radius_positive small_error room
      (first_outer ⟨first_height.1.le, first_height.2.le⟩)
    have first_centered : B.sectorFrame i (actual - D.projectedMap Q (origin)) =
        data.value (S.upper.point slice.upperHeight) - data.center := by
      change data.outputFrame (actual - D.projectedMap Q (origin)) = _
      rw [map_sub, ← data.center_eq_outputFrame]
      exact congrArg (fun z => z - data.center) (data.outputFrame.apply_symm_apply _)
    have last_centered : B.sectorFrame j (actual - D.projectedMap Q (origin)) =
        other.value (T.lower.point other_slice.lowerHeight) - other.center := by
      change other.outputFrame (actual - D.projectedMap Q (origin)) = _
      dsimp only [actual]
      rw [common.2, map_sub, LinearIsometryEquiv.apply_symm_apply, ← other.center_eq_outputFrame]
    have size : ‖actual - D.projectedMap Q (origin)‖ ≤ radius := by
      rw [data.outputFrame_symm_source_distance]
      exact slice.upper_radius.le
    have equal : p = actual := B.inner_barrier_point_eq_of_norm_le i j
      (D.projectedMap Q (origin)) actual p
      (margins i (Or.inl rfl)) (margins j (Or.inr rfl))
      ⟨first.1, first.2.1⟩ ⟨last.1, last.2.1⟩
      (by rw [first_centered]; exact first.2.2.1)
      (by rw [last_centered]; exact last.2.2.1)
      (size.trans_eq first.2.2.2.symm)
    exact ⟨equal, common.2, common.1⟩
  · have first_height := (data.circle_slice_heights radius_positive far slice).2
    have last_height := (other.circle_slice_heights radius_positive far other_slice).1
    have at_root := first_outer ⟨first_height.1.le, first_height.2.le⟩
    have cones := shared_sector_bank_mem_both_cones positive small i j true shared first_height.1
    have first_cone : origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point slice.upperHeight) - origin ∈ closedFiveSector t i := by
      rw [add_sub_cancel_left, at_root]
      exact cones.1
    have last_cone : origin + (fiveSectorFrame t positive small i).place.symm
        (S.upper.point slice.upperHeight) - origin ∈ closedFiveSector t j := by
      rw [add_sub_cancel_left, at_root]
      exact cones.2
    have boundary : ∀ a, origin +
        (fiveSectorFrame t positive small i).place.symm (S.upper.point slice.upperHeight) -
          origin ∉ strictFiveSector t a := by
      rw [add_sub_cancel_left, at_root]
      exact (fiveSector_enclosingStrip_bank_not_strict_any positive small i first_height.1.le).2
    have inside := deep (Metric.ball_subset_closedBall
      (data.closed_circle_point_mem_ball small_error slice.upper_closed slice.upper_radius far))
    obtain ⟨_, w, at_seed, _, seed_member⟩ :=
      M.fine_coherent_seed_of_boundary_component F covered positive small Q D leaf_vertices
        leaf_coherent c member inside boundary
    have seed_first :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone seed_member
    have seed_last :=
      (F.componentTail c).position_inDirectionWedge_of_mem member last_cone seed_member
    obtain ⟨k, s, child, physical, matching, size⟩ :=
      M.upper_circle_bank_on_component_in_sweep_with_physical F covered
      R outward D B w c unattached at_seed footprint i seed_first data slice radius_positive far
      outside small_error deep member
    obtain ⟨l, r, other_child, other_physical, other_matching, other_size⟩ :=
      M.lower_circle_bank_on_component_in_sweep_with_physical F covered R outward D B w c
        unattached at_seed
        footprint j seed_last other other_slice radius_positive far outside small_error deep
        other_member
    have first_inside :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone child
    have last_inside := (F.componentTail c).position_inDirectionWedge_of_mem member last_cone child
    have exit_margins := B.circle_shared_bank_margins i j true shared positive_margin face_bounds
      data slice radius_positive small_error room at_root
    change ∀ a, a = i ∨ a = j →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (origin))).re ∧
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (origin))).im at exit_margins
    rw [matching] at exit_margins
    have entrance_margins := B.circle_shared_bank_margins j i false shared positive_margin
      face_bounds
      other other_slice radius_positive small_error room
      (last_outer ⟨last_height.1.le, last_height.2.le⟩)
    change ∀ a, a = j ∨ a = i →
      0 < (B.sectorFrame a (other.outputFrame.symm
        (other.value (T.lower.point other_slice.lowerHeight)) -
          D.projectedMap Q (origin))).re ∧
      0 < (B.sectorFrame a (other.outputFrame.symm
        (other.value (T.lower.point other_slice.lowerHeight)) -
          D.projectedMap Q (origin))).im at entrance_margins
    rw [other_matching] at entrance_margins
    have first_centered : data.value (S.upper.point slice.upperHeight) - data.center =
        B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w k)
          (1 - (s : ℝ)) - D.projectedMap Q (origin)) := by
      have value := congrArg data.outputFrame matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, data.center_eq_outputFrame, map_sub]
      rfl
    have last_centered : other.value (T.lower.point other_slice.lowerHeight) - other.center =
        B.sectorFrame j (R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w l)
          (1 - (r : ℝ)) - D.projectedMap Q (origin)) := by
      have value := congrArg other.outputFrame other_matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, other.center_eq_outputFrame, map_sub]
      rfl
    have contact := M.weak_circle_caps_contact_values_of_component_bank_bounds F covered R
      (R.completedBankChain w k) (R.completedBankChain w l) c unattached child other_child positive
      small outward footprint i j first_inside last_inside curvature_covered D B budget s r
      (D.projectedMap Q (origin)) size.le other_size.le
      (fun a choice => ⟨exit_margins a choice, entrance_margins a choice.symm⟩)
      (by rw [← first_centered]) (by rw [← last_centered]) ⟨first, last⟩
    have physical_equal := M.unattached_component_bank_contact_same_projected_point F covered
       R
      (R.completedBankChain w k) (R.completedBankChain w l) c unattached child other_child positive
      small outward footprint i first_inside curvature_covered D B budget s r contact.2
    have endpoints := physical.trans (physical_equal.trans other_physical.symm)
    refine ⟨contact.1.trans matching.symm, matching.trans (contact.2.trans other_matching.symm), ?_⟩
    exact add_left_cancel endpoints

/-- Actual closed traces at facing outer banks identify one physical surface point,
including when the shared sector ray itself carries a cut. -/
theorem closed_circle_shared_outer_physical_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (leaf_coherent : ∀ a, ∀ leaf : M.GeometricSectorLeaf F covered positive small a,
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    (footprint : Q.footprint = outerDomain)
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
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_outer : Set.EqOn S.upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (last_outer : Set.EqOn T.lower.point
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point (Set.Icc 0 cutoff))
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    {ω : ℝ} (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (origin) cutoff →
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).re ∧
      ω * ‖p - origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (origin))).im)
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    {x y : ℂ} (first : x ∈ closure (S.openSlab 0 cutoff))
    (last : y ∈ closure (T.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius)
    (same : data.outputFrame.symm (data.value x) = other.outputFrame.symm (other.value y)) :
    (fiveSectorFrame t positive small i).place.symm x =
      (fiveSectorFrame t positive small j).place.symm y := by
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  have other_size : ‖other.value y - other.center‖ = radius := by
    rw [← other.outputFrame_symm_source_distance, ← same,
      data.outputFrame_symm_source_distance]
    exact size
  have first_caps := B.closed_circle_image_subset_weak_caps i data slice first_order first_error
    first_margin radius_positive far ⟨data.value x, ⟨⟨x, first, rfl⟩, size⟩, rfl⟩
  have last_caps := B.closed_circle_image_subset_weak_caps j other other_slice last_order last_error
    last_margin radius_positive far ⟨other.value y, ⟨⟨y, last, rfl⟩, other_size⟩, same.symm⟩
  have contact := M.weak_circle_outer_banks_contact F covered positive small R outward D B
    leaf_vertices leaf_coherent footprint curvature_covered budget shared data other slice
    other_slice first_outer last_outer radius_positive small_error room outside deep
    positive_margin face_bounds first_caps.1 last_caps.2
  have first_subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_subset : T.openSlab 0 cutoff ⊆ other.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_value : data.value x = data.value (S.upper.point slice.upperHeight) :=
    data.outputFrame.symm.injective contact.1
  have last_value : other.value y = other.value (T.lower.point other_slice.lowerHeight) :=
    other.outputFrame.symm.injective (same.symm.trans (contact.1.trans contact.2.1))
  have first_point := data.closed_injective (closure_mono first_subset first)
    slice.upper_closed first_value
  have last_point := other.closed_injective (closure_mono last_subset last)
    other_slice.lower_closed last_value
  rw [first_point, last_point]
  exact contact.2.2

end Unfoldings.ConvexRoof.SectorForest
