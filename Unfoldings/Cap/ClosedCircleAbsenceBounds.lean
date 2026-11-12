module

public import Unfoldings.Cap.RadialClosedCircleSections
public import Unfoldings.Geometry.MonotoneStripSourceError

/-! Absent closed circle sections leave the entire actual approached strip strictly inside. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- A closed monotone connector crosses every controlled radius below a closed point.
Pinches remain in its actual closure, so no finite exceptional set is needed. -/
theorem closed_circle_nonempty_of_norm_ge {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    {q : ℂ} (member : q ∈ closure (S.openSlab 0 cutoff))
    (large : radius ≤ ‖data.value q - data.center‖) :
    (data.value '' closure (S.openSlab 0 cutoff) ∩
      {z | ‖z - data.center‖ = radius}).Nonempty := by
  have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have closed := closure_mono subset member
  have bounded := data.closed_bounded closed
  obtain ⟨active, active_member⟩ := closure_nonempty_iff.mp ⟨q, closed⟩
  have source_value := data.source_value_of_active active_member
  have coordinates := S.carrier_coordinates_nonnegative data.lower_source data.upper_source
    bounded.1 bounded.2.1
  have source_member : (0 : ℂ) ∈ S.carrier := by
    change S.lower.coordinate (0 + 0) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ S.upper.coordinate (0 + 0)
    rw [zero_add, data.lower_source, data.upper_source]
    exact ⟨le_rfl, le_rfl⟩
  let P := S.increasingPath source_member bounded.1 coordinates.1 coordinates.2
  have inside (s : unitInterval) : P s ∈ closure data.strictDomain := by
    have in_bounds := S.increasingPath_mem_bounded
      (show (0 : ℂ) ∈ S.boundedCarrier 0 (q.re + q.im) from
        ⟨source_member, by
          simpa only [Complex.zero_re, Complex.zero_im, zero_add] using
            (show (0 : ℝ) ∈ Set.Icc 0 (q.re + q.im) from ⟨le_rfl, bounded.2.1⟩)⟩)
      (show q ∈ S.boundedCarrier 0 (q.re + q.im) from ⟨bounded.1, bounded.2.1, le_rfl⟩)
      coordinates.1 coordinates.2 s
    exact data.closed_initial closed in_bounds.1 in_bounds.2
  let norm_value := fun s : unitInterval => ‖data.value (P s) - data.center‖
  have continuous : Continuous norm_value :=
    ((data.continuous.comp P.continuous).sub continuous_const).norm
  have first : norm_value 0 = 0 := by
    change ‖data.value (P 0) - data.center‖ = 0
    rw [P.source, source_value, sub_self, norm_zero]
  have last : radius ≤ norm_value 1 := by
    change radius ≤ ‖data.value (P 1) - data.center‖
    rw [P.target]
    exact large
  obtain ⟨s, _, size⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ 1 from zero_le_one) continuous.continuousOn
    ⟨by rw [first]; exact radius_positive.le, last⟩
  have approached := data.closed_circle_point_mem_closure_openSlab radius_positive far
    (inside s) size
  exact ⟨data.value (P s), ⟨P s, approached, rfl⟩, size⟩

/-- Removing every closed contact, rather than only the open slice, gives strict enclosure
at every radius. Coherent pinch radii elsewhere in the mesh are irrelevant. -/
theorem closed_inside_of_empty_closed_circle {radius : ℝ} (radius_positive : 0 < radius)
    (far : radius < (1 / 2 - ε) * cutoff)
    (empty : data.value '' closure (S.openSlab 0 cutoff) ∩
      {z | ‖z - data.center‖ = radius} = ∅)
    {q : ℂ} (member : q ∈ closure (S.openSlab 0 cutoff)) :
    ‖data.value q - data.center‖ < radius := by
  by_contra large
  have present := data.closed_circle_nonempty_of_norm_ge radius_positive far member
    (le_of_not_gt large)
  rw [empty] at present
  exact Set.not_nonempty_empty present

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
