module

public import Unfoldings.Cap.ClosedCircleSectionDegeneracy
public import Unfoldings.Cap.StripCircleClosedBounds
public import Unfoldings.Cap.RadialStripBankOrder

/-! Both genuine and collapsed closed circle sections bound every actual approached circle point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  (sectionData : S.ClosedBankCircleSection data.value data.center cutoff radius)
  {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
  (numerical : ε * (1 + ε) < μ - ε)
  (linear_error : ∀ f z,
    ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
      z‖ ≤ ε * ‖z‖)
  (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
    μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include nonnegative small_error numerical linear_error margin radius_positive far

/-- A zero-width section supplies the same weak bounds as a genuine interval of circle points. -/
theorem closed_circle_section_point_bounds {x : ℂ}
    (closed : x ∈ closure (S.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius) :
    (data.value (S.lower.point sectionData.lowerHeight) - data.center).re ≤
        (data.value x - data.center).re ∧
      (data.value x - data.center).re ≤
        (data.value (S.upper.point sectionData.upperHeight) - data.center).re ∧
      (data.value x - data.center).im ≤
        (data.value (S.lower.point sectionData.lowerHeight) - data.center).im := by
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  by_cases meets : (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}).Nonempty
  · obtain ⟨slice⟩ := data.circle_slice close_margin margin radius_positive far meets
    have values := data.closed_circle_section_values_eq close_margin margin radius_positive far
      sectionData slice.toClosedSection
    change data.value (S.lower.point sectionData.lowerHeight) =
        data.value (S.lower.point slice.lowerHeight) ∧
      data.value (S.upper.point sectionData.upperHeight) =
        data.value (S.upper.point slice.upperHeight) at values
    rw [values.1, values.2]
    have subset : S.openSlab 0 cutoff ⊆ data.strictDomain :=
      fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
    have actual_closed := closure_mono subset closed
    obtain ⟨active, active_member⟩ := closure_nonempty_iff.mp ⟨x, actual_closed⟩
    have quadrant := data.strict_quadrant_of_closed_margin close_margin margin actual_closed
      (data.closed_circle_height_mem_Ioo radius_positive far actual_closed size).1
    have lower_quadrant := data.strict_quadrant_of_closed_margin close_margin margin
      slice.lower_closed
      (data.closed_circle_height_mem_Ioo radius_positive far
        slice.lower_closed slice.lower_radius).1
    have upper_quadrant := data.strict_quadrant_of_closed_margin close_margin margin
      slice.upper_closed
      (data.closed_circle_height_mem_Ioo radius_positive far
        slice.upper_closed slice.upper_radius).1
    have ordered := (data.bank_circle_order nonnegative small_error numerical linear_error margin
      radius_positive slice.lower_closed slice.upper_closed slice.lower_radius slice.upper_radius
      slice.distinct).1
    exact slice.closed_circle_image_weak_bounds data.continuous data.closed_injective
      (fun z member ends => data.end_levels_avoid_circle active_member radius_positive far member
        ends) (data.circle_interval close_margin margin radius_positive far) ordered
      ⟨lower_quadrant.1.le, lower_quadrant.2.le⟩ ⟨upper_quadrant.1.le, upper_quadrant.2.le⟩
      ⟨quadrant.1.le, quadrant.2.le⟩ ⟨⟨x, closed, rfl⟩, size⟩
  · have empty := Set.not_nonempty_iff_eq_empty.mp meets
    have first := data.closed_circle_point_mem_closure_openSlab radius_positive far
      sectionData.lower_closed sectionData.lower_radius
    have last := data.closed_circle_point_mem_closure_openSlab radius_positive far
      sectionData.upper_closed sectionData.upper_radius
    have first_value := congrArg data.value (data.closed_circle_preimages_eq_of_empty
      radius_positive far empty first closed sectionData.lower_radius size)
    have last_value := congrArg data.value (data.closed_circle_preimages_eq_of_empty
      radius_positive far empty last closed sectionData.upper_radius size)
    rw [first_value, last_value]
    exact ⟨le_rfl, le_rfl, le_rfl⟩

theorem closed_circle_section_banks_ordered :
    (data.value (S.lower.point sectionData.lowerHeight) - data.center).re ≤
      (data.value (S.upper.point sectionData.upperHeight) - data.center).re :=
  (data.closed_circle_section_point_bounds sectionData nonnegative small_error numerical
    linear_error
    margin radius_positive far
    (data.closed_circle_point_mem_closure_openSlab radius_positive far sectionData.lower_closed
      sectionData.lower_radius) sectionData.lower_radius).2.1

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
