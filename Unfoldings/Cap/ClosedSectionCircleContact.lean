module

public import Unfoldings.Cap.ClosedCircleSectionBounds
public import Unfoldings.Geometry.ClosedCircleCapsContact

/-! Ordered closed sections identify facing physical endpoints, including pinches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S T : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)
  (other : N.RadialStripTraceData positive small D calibration i T ε cutoff)

/-- A weak facing-bank order suffices even when a section consists only of a pinch point. -/
theorem closed_section_contact_preimages_eq_bank_points
    (first_section : S.ClosedBankCircleSection data.value data.center cutoff radius)
    (last_section : T.ClosedBankCircleSection other.value other.center cutoff radius)
    {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (facing_order : (data.value (S.upper.point first_section.upperHeight) - data.center).re ≤
      (other.value (T.lower.point last_section.lowerHeight) - other.center).re)
    {x y : ℂ} (first : x ∈ closure (S.openSlab 0 cutoff))
    (last : y ∈ closure (T.openSlab 0 cutoff))
    (size : ‖data.value x - data.center‖ = radius)
    (same : data.value x = other.value y) :
    x = S.upper.point first_section.upperHeight ∧ y = T.lower.point last_section.lowerHeight := by
  have centers : data.center = other.center := rfl
  have last_size : ‖other.value y - other.center‖ = radius := by
    rw [← same, ← centers]
    exact size
  have first_bounds := data.closed_circle_section_point_bounds first_section nonnegative
    small_error numerical linear_error first_margin radius_positive far first size
  have last_bounds := other.closed_circle_section_point_bounds last_section nonnegative
    small_error numerical linear_error last_margin radius_positive far last last_size
  have first_re : (data.value x - data.center).re =
      (data.value (S.upper.point first_section.upperHeight) - data.center).re := by
    apply le_antisymm first_bounds.2.1
    apply facing_order.trans
    simpa only [← centers, ← same] using last_bounds.1
  have last_re : (other.value y - other.center).re =
      (other.value (T.lower.point last_section.lowerHeight) - other.center).re := by
    apply le_antisymm _ last_bounds.1
    apply le_trans _ facing_order
    simpa only [← centers, ← same] using first_bounds.2.1
  have subset_first : S.openSlab 0 cutoff ⊆ data.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have subset_last : T.openSlab 0 cutoff ⊆ other.strictDomain :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  have first_closed := closure_mono subset_first first
  have last_closed := closure_mono subset_last last
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have first_quadrant := data.strict_quadrant_of_closed_margin close_margin first_margin
    first_closed
    (data.closed_circle_height_mem_Ioo radius_positive far first_closed size).1
  have first_bank_quadrant := data.strict_quadrant_of_closed_margin close_margin first_margin
    first_section.upper_closed (data.closed_circle_height_mem_Ioo radius_positive far
      first_section.upper_closed first_section.upper_radius).1
  have last_quadrant := other.strict_quadrant_of_closed_margin close_margin last_margin last_closed
    (other.closed_circle_height_mem_Ioo radius_positive far last_closed last_size).1
  have last_bank_quadrant := other.strict_quadrant_of_closed_margin close_margin last_margin
    last_section.lower_closed (other.closed_circle_height_mem_Ioo radius_positive far
      last_section.lower_closed last_section.lower_radius).1
  have first_equal := complex_eq_of_norm_re_eq
    (size.trans first_section.upper_radius.symm) first_re first_quadrant.2.le
    first_bank_quadrant.2.le
  have last_equal := complex_eq_of_norm_re_eq
    (last_size.trans last_section.lower_radius.symm) last_re last_quadrant.2.le
    last_bank_quadrant.2.le
  exact ⟨data.closed_injective first_closed first_section.upper_closed
      (sub_left_inj.mp first_equal),
    other.closed_injective last_closed last_section.lower_closed (sub_left_inj.mp last_equal)⟩

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
