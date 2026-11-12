module

public import Unfoldings.Cap.StripCircleClosedBounds
public import Unfoldings.Cap.CrossFrameStripCircleBounds
public import Unfoldings.Cap.RadialStripCircleInterval
public import Unfoldings.Geometry.WeakCircleCaps

/-! Actual approached closed strip-circle images retain both weak endpoint barriers. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (slice : S.BankCircleSlice data.value data.center cutoff radius)
  (ordered : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
    (data.value (S.upper.point slice.upperHeight) - data.center).re)
  {μ : ℝ} (small_error : ε < μ)
  (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include ordered small_error margin radius_positive far

theorem circle_image_closed_bank_bounds {p : Plane}
    (member : p ∈ data.outputFrame.symm '' (data.value '' closure (S.openSlab 0 cutoff) ∩
      {z | ‖z - data.center‖ = radius})) :
    0 < (B.sectorFrame i (p - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame i (p - D.projectedMap K source)).im ∧
      (B.sectorFrame i (p - D.projectedMap K source)).re ≤
        (data.value (S.upper.point slice.upperHeight) - data.center).re ∧
      (B.sectorFrame i (p - D.projectedMap K source)).im ≤
        (data.value (S.lower.point slice.lowerHeight) - data.center).im ∧
      ‖p - D.projectedMap K source‖ = radius := by
  obtain ⟨_, ⟨⟨x, approached, rfl⟩, size⟩, at_p⟩ := member
  have domain_subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed : x ∈ closure data.strictDomain := closure_mono domain_subset approached
  have nonempty : data.strictDomain.Nonempty := closure_nonempty_iff.mp ⟨x, closed⟩
  obtain ⟨active, active_member⟩ := nonempty
  have height := data.closed_height_pos_of_norm closed (by rw [size]; exact radius_positive)
  have quadrant := data.strict_quadrant_of_closed_margin small_error margin closed height
  have lower_height := data.closed_height_pos_of_norm slice.lower_closed
    (by rw [slice.lower_radius]; exact radius_positive)
  have upper_height := data.closed_height_pos_of_norm slice.upper_closed
    (by rw [slice.upper_radius]; exact radius_positive)
  have lower_quadrant := data.strict_quadrant_of_closed_margin small_error margin
    slice.lower_closed lower_height
  have upper_quadrant := data.strict_quadrant_of_closed_margin small_error margin
    slice.upper_closed upper_height
  have bounds := slice.closed_circle_image_weak_bounds data.continuous data.closed_injective
    (fun z member ends =>
      data.end_levels_avoid_circle active_member radius_positive far member ends)
    (data.circle_interval small_error margin radius_positive far) ordered
    ⟨lower_quadrant.1.le, lower_quadrant.2.le⟩ ⟨upper_quadrant.1.le, upper_quadrant.2.le⟩
    ⟨quadrant.1.le, quadrant.2.le⟩ ⟨⟨x, approached, rfl⟩, size⟩
  have centered : B.sectorFrame i (p - D.projectedMap K source) =
      data.value x - data.center := by
    change data.outputFrame (p - D.projectedMap K source) = _
    rw [← at_p, map_sub, LinearIsometryEquiv.apply_symm_apply, ← data.center_eq_outputFrame]
  have physical_size : ‖p - D.projectedMap K source‖ = radius := by
    rw [← at_p, data.outputFrame_symm_source_distance]
    exact size
  rw [centered]
  exact ⟨quadrant.1, quadrant.2, bounds.2.1, bounds.2.2, physical_size⟩

theorem closed_circle_image_subset_weak_caps :
    data.outputFrame.symm '' (data.value '' closure (S.openSlab 0 cutoff) ∩
        {z | ‖z - data.center‖ = radius}) ⊆
      weakCircleUpperCap (B.sectorFrame i) (D.projectedMap K source) radius
          (data.value (S.upper.point slice.upperHeight) - data.center).re ∩
        weakCircleLowerCap (B.sectorFrame i) (D.projectedMap K source) radius
          (data.value (S.lower.point slice.lowerHeight) - data.center).im := by
  intro p member
  have bounds := B.circle_image_closed_bank_bounds i data slice ordered small_error margin
    radius_positive far member
  exact ⟨⟨bounds.1.le, bounds.2.1, bounds.2.2.1, bounds.2.2.2.2⟩,
    ⟨bounds.1.le, bounds.2.1, bounds.2.2.2.1, bounds.2.2.2.2⟩⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
