module

public import Unfoldings.Cap.OuterCircleContactAlternative
public import Unfoldings.Cap.BoundaryComponentFineSeed
public import Unfoldings.Cap.SharedEndpointCircleSeparation
public import Unfoldings.Cap.SharedBoundaryBankMargins
public import Unfoldings.Cap.ComponentBankCircleSeparation
public import Unfoldings.Cap.RadialComponentCircleBanks

/-! Adjacent outer surviving strips separate even when their shared ray is cut. -/

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

theorem circle_images_disjoint_across_shared_outer_banks
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
    (budget : FineC.totalInteriorAngularDefect Set.univ ≤ Real.pi)
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
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν ω : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (small_error : ε < 1 / 2)
    (room : 2 * radius < (1 / 2 - ε) * cutoff)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (positive_margin : 0 < ω)
    (face_bounds : ∀ a f p, p ∈ (Q.projectedTriangle f).carrier →
      p - K.projectedVertex origin ∈ closedFiveSector t a →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ω * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame a (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have far : radius < (1 / 2 - ε) * cutoff := by linarith
  rcases M.outer_circle_endpoints_eq_or_common_component F covered positive small lower R D
    leaf_coherent data other slice other_slice shared first_outer last_outer radius_positive
    far deep
    with common | ⟨c, member, other_member, unattached⟩
  · exact B.circle_images_disjoint_of_shared_endpoint i j data other slice other_slice first_order
      last_order first_error last_error first_margin last_margin radius_positive common
  · have first_height := (data.circle_slice_heights radius_positive far slice).2
    have last_height := (other.circle_slice_heights radius_positive far other_slice).1
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
    obtain ⟨_, w, at_seed, _, seed_member⟩ :=
      M.fine_coherent_seed_of_boundary_component F covered positive small lower Q D leaf_vertices
        leaf_coherent c member inside boundary
    have seed_first :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone seed_member
    have seed_last :=
      (F.componentTail c).position_inDirectionWedge_of_mem member last_cone seed_member
    obtain ⟨k, s, child, matching, size⟩ :=
      M.upper_circle_bank_on_component_in_sweep F covered lower
      R outward D B w c unattached at_seed footprint i seed_first data slice radius_positive far
      outside small_error deep member
    obtain ⟨l, r, other_child, other_matching, other_size⟩ :=
      M.lower_circle_bank_on_component_in_sweep F covered lower R outward D B w c unattached at_seed
        footprint j seed_last other other_slice radius_positive far outside small_error deep
        other_member
    have first_inside :=
      (F.componentTail c).position_inDirectionWedge_of_mem member first_cone child
    have last_inside := (F.componentTail c).position_inDirectionWedge_of_mem member last_cone child
    have exit_margins := B.circle_shared_bank_margins i j true shared positive_margin face_bounds
      data slice radius_positive small_error room at_root
    change ∀ a, a = i ∨ a = j →
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).re ∧
      0 < (B.sectorFrame a (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) -
        D.projectedMap Q (K.projectedVertex origin))).im at exit_margins
    rw [matching] at exit_margins
    have entrance_margins := B.circle_shared_bank_margins j i false shared positive_margin
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
        B.sectorFrame i (R.parentExitPoint (R.completedDevelopment D) (R.completedBankChain w k)
          (1 - (s : ℝ)) - D.projectedMap Q (K.projectedVertex origin)) := by
      have value := congrArg data.outputFrame matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, data.center_eq_outputFrame, map_sub]
      rfl
    have last_centered : other.value (T.lower.point other_slice.lowerHeight) - other.center =
        B.sectorFrame j (R.parentEntrancePoint (R.completedDevelopment D) (R.completedBankChain w l)
          (1 - (r : ℝ)) - D.projectedMap Q (K.projectedVertex origin)) := by
      have value := congrArg other.outputFrame other_matching
      rw [LinearIsometryEquiv.apply_symm_apply] at value
      rw [value, other.center_eq_outputFrame, map_sub]
      rfl
    apply M.circle_images_disjoint_of_component_bank_bounds F covered lower R
      (R.completedBankChain w k) (R.completedBankChain w l) c unattached child other_child positive
      small outward footprint i j first_inside last_inside curvature_covered D B data other slice
      other_slice first_order last_order first_error last_error first_margin last_margin
      radius_positive budget s r size.le other_size.le
    · intro a choice
      exact ⟨exit_margins a choice, entrance_margins a choice.symm⟩
    · rw [← first_centered]
    · rw [← last_centered]

end Unfoldings.ConvexCap.SectorForest
