module

public import Unfoldings.Cap.ClosedStripCircleCaps
public import Unfoldings.Geometry.ClosedCircleCapsContact

/-! Actual closed strip-circle contacts occur only at their named facing bank endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

/-- The bank order already obtained by the waterfall survivor theorem also controls
closed image contacts, without assuming strict separation of the facing endpoints. -/
theorem closed_circle_images_contact_eq_bank_endpoints (i : FiveSector)
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
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
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (facing_order : (data.value (S.upper.point slice.upperHeight) - data.center).re ≤
      (other.value (T.lower.point other_slice.lowerHeight) - other.center).re)
    {p : Plane}
    (first : p ∈ data.outputFrame.symm ''
      (data.value '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - data.center‖ = radius}))
    (last : p ∈ other.outputFrame.symm ''
      (other.value '' closure (T.openSlab 0 cutoff) ∩ {z | ‖z - other.center‖ = radius})) :
    p = data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) ∧
      data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)) =
        other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight)) := by
  have first_caps := B.closed_circle_image_subset_weak_caps i data slice first_order first_error
    first_margin radius_positive far first
  have last_caps := B.closed_circle_image_subset_weak_caps i other other_slice last_order last_error
    last_margin radius_positive far last
  have first_centered (z : ℂ) : B.sectorFrame i
      (data.outputFrame.symm z - D.projectedMap K source) = z - data.center := by
    change data.outputFrame (data.outputFrame.symm z - D.projectedMap K source) = _
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← data.center_eq_outputFrame]
  have last_centered (z : ℂ) : B.sectorFrame i
      (other.outputFrame.symm z - D.projectedMap K source) = z - other.center := by
    change other.outputFrame (other.outputFrame.symm z - D.projectedMap K source) = _
    rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← other.center_eq_outputFrame]
  have upper_height := data.closed_height_pos_of_norm slice.upper_closed
    (by rw [slice.upper_radius]; exact radius_positive)
  have lower_height := other.closed_height_pos_of_norm other_slice.lower_closed
    (by rw [other_slice.lower_radius]; exact radius_positive)
  have upper_quadrant := data.strict_quadrant_of_closed_margin first_error first_margin
    slice.upper_closed upper_height
  have lower_quadrant := other.strict_quadrant_of_closed_margin last_error last_margin
    other_slice.lower_closed lower_height
  apply weak_circle_caps_contact_eq_of_horizontal_order (B.sectorFrame i)
    (D.projectedMap K source)
    (data.outputFrame.symm (data.value (S.upper.point slice.upperHeight)))
    (other.outputFrame.symm (other.value (T.lower.point other_slice.lowerHeight)))
    (radius := radius)
  · rw [data.outputFrame_symm_source_distance]
    exact slice.upper_radius
  · rw [other.outputFrame_symm_source_distance]
    exact other_slice.lower_radius
  · rw [first_centered]
    exact ⟨upper_quadrant.1.le, upper_quadrant.2.le⟩
  · rw [last_centered]
    exact ⟨lower_quadrant.1.le, lower_quadrant.2.le⟩
  · rw [first_centered, last_centered]
    exact facing_order
  · rw [first_centered]
    exact first_caps.1
  · rw [last_centered]
    exact last_caps.2

/-- The contact classification identifies physical strip coordinates as well as values. -/
theorem closed_circle_contact_preimages_eq_bank_points (i : FiveSector)
    {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i T ε cutoff)
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
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (facing_order : (data.value (S.upper.point slice.upperHeight) - data.center).re ≤
      (other.value (T.lower.point other_slice.lowerHeight) - other.center).re)
    {x y : ℂ} (first : x ∈ closure (S.openSlab 0 cutoff))
    (last : y ∈ closure (T.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius)
    (same : data.outputFrame.symm (data.value x) = other.outputFrame.symm (other.value y)) :
    x = S.upper.point slice.upperHeight ∧ y = T.lower.point other_slice.lowerHeight := by
  have other_size : ‖other.value y - other.center‖ = radius := by
    rw [← other.outputFrame_symm_source_distance, ← same,
      data.outputFrame_symm_source_distance]
    exact size
  have values := B.closed_circle_images_contact_eq_bank_endpoints i data other slice other_slice
    first_order last_order first_error last_error first_margin last_margin radius_positive far
    facing_order ⟨data.value x, ⟨⟨x, first, rfl⟩, size⟩, rfl⟩
    ⟨other.value y, ⟨⟨y, last, rfl⟩, other_size⟩, same.symm⟩
  have first_subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have last_subset : T.openSlab 0 cutoff ⊆ other.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_value : data.value x = data.value (S.upper.point slice.upperHeight) :=
    data.outputFrame.symm.injective values.1
  have last_value : other.value y = other.value (T.lower.point other_slice.lowerHeight) :=
    other.outputFrame.symm.injective (same.symm.trans (values.1.trans values.2))
  exact ⟨data.closed_injective (closure_mono first_subset first) slice.upper_closed first_value,
    other.closed_injective (closure_mono last_subset last) other_slice.lower_closed last_value⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
