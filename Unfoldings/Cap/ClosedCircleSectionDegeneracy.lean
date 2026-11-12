module

public import Unfoldings.Cap.RadialClosedCircleSections

/-! Closed circle sections collapse exactly at absent open-circle slices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  {μ : ℝ} (small_error : ε < μ)
  (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include small_error margin radius_positive far

/-- Radial uniqueness makes bank values independent of the chosen closed section. -/
theorem closed_circle_section_values_eq
    (first last : S.ClosedBankCircleSection data.value data.center cutoff radius) :
    data.value (S.lower.point first.lowerHeight) = data.value (S.lower.point last.lowerHeight) ∧
      data.value (S.upper.point first.upperHeight) =
        data.value (S.upper.point last.upperHeight) := by
  obtain ⟨_, _, lower, upper, _⟩ := data.circle_interval small_error margin radius_positive far
  exact ⟨(lower first.lowerHeight first.lower_bounds first.lower_closed first.lower_radius).trans
      (lower last.lowerHeight last.lower_bounds last.lower_closed last.lower_radius).symm,
    (upper first.upperHeight first.upper_bounds first.upper_closed first.upper_radius).trans
      (upper last.upperHeight last.upper_bounds last.upper_closed last.upper_radius).symm⟩

/-- A collapsed section is exactly a closed-only circle contact; genuine slices stay distinct. -/
theorem closed_circle_section_values_eq_iff_empty
    (sectionData : S.ClosedBankCircleSection data.value data.center cutoff radius) :
    data.value (S.lower.point sectionData.lowerHeight) =
        data.value (S.upper.point sectionData.upperHeight) ↔
      data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅ := by
  constructor
  · intro equal
    by_contra nonempty
    obtain ⟨slice⟩ := data.circle_slice small_error margin radius_positive far
      (Set.nonempty_iff_ne_empty.mpr nonempty)
    have values := data.closed_circle_section_values_eq small_error margin radius_positive far
      sectionData slice.toClosedSection
    exact slice.distinct (values.1.symm.trans (equal.trans values.2))
  · intro empty
    have first := data.closed_circle_point_mem_closure_openSlab radius_positive far
      sectionData.lower_closed sectionData.lower_radius
    have last := data.closed_circle_point_mem_closure_openSlab radius_positive far
      sectionData.upper_closed sectionData.upper_radius
    exact congrArg data.value (data.closed_circle_preimages_eq_of_empty radius_positive far empty
      first last sectionData.lower_radius sectionData.upper_radius)

/-- Degenerate section labels retain one physical point, not merely equal developed endpoints. -/
theorem closed_circle_section_points_eq_iff_empty
    (sectionData : S.ClosedBankCircleSection data.value data.center cutoff radius) :
    S.lower.point sectionData.lowerHeight = S.upper.point sectionData.upperHeight ↔
      data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius} = ∅ := by
  rw [← data.closed_circle_section_values_eq_iff_empty small_error margin radius_positive far
    sectionData]
  exact ⟨congrArg data.value, data.closed_injective sectionData.lower_closed
    sectionData.upper_closed⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
