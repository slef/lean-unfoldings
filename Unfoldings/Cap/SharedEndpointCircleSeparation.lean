module

public import Unfoldings.Cap.CrossFrameStripCircleBounds

/-! A common actual circle endpoint separates open arcs expressed in different frames. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

theorem circle_images_disjoint_of_shared_endpoint
    (i j : FiveSector) {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) j T ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius)
    (common : data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
      other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight))) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  let actual := data.outputFrame.symm (data.value (S.upper.point slice.upperHeight))
  have first_centered : B.sectorFrame i (actual - D.projectedMap K source) =
      data.value (S.upper.point slice.upperHeight) - data.center := by
    change data.outputFrame (actual - D.projectedMap K source) = _
    rw [map_sub, ← data.center_eq_outputFrame]
    exact congrArg (fun z => z - data.center) (data.outputFrame.apply_symm_apply _)
  have last_centered : B.sectorFrame j (actual - D.projectedMap K source) =
      other.value (T.lower.point other_slice.lowerHeight) - other.center := by
    change other.outputFrame (actual - D.projectedMap K source) = _
    dsimp only [actual]
    rw [common, map_sub, LinearIsometryEquiv.apply_symm_apply, ← other.center_eq_outputFrame]
  have first_height := data.closed_height_pos_of_norm slice.upper_closed
    (by rw [slice.upper_radius]; exact radius_positive)
  have last_height := other.closed_height_pos_of_norm other_slice.lower_closed
    (by rw [other_slice.lower_radius]; exact radius_positive)
  have first_quadrant := data.strict_quadrant_of_closed_margin first_error first_margin
    slice.upper_closed first_height
  have last_quadrant := other.strict_quadrant_of_closed_margin last_error last_margin
    other_slice.lower_closed last_height
  have size : ‖actual - D.projectedMap K source‖ = radius := by
    rw [data.outputFrame_symm_source_distance]
    exact slice.upper_radius
  apply Set.disjoint_left.mpr
  intro p first last
  have left := B.circle_image_open_bank_bounds i data slice first_order first_error first_margin
    radius_positive first
  have right := B.circle_image_open_bank_bounds j other other_slice last_order last_error
    last_margin
    radius_positive last
  apply B.inner_barrier_point_exclusion_of_norm_le i j (D.projectedMap K source) actual p
    (by rwa [first_centered]) (by rwa [last_centered]) ⟨left.1.le, left.2.1⟩
    ⟨right.1.le, right.2.1⟩
  · rw [first_centered]
    exact left.2.2.1
  · rw [last_centered]
    exact right.2.2.2.1
  · exact size.le.trans_eq left.2.2.2.2.symm

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
