module

public import Unfoldings.Cap.ClosedCircleSectionBounds
public import Unfoldings.Geometry.WeakCircleCaps
public import Mathlib.Order.Prod.Lex.Basic

/-! Collapsed closed sections preserve physical labels in the same finite bank-order interface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff radius : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- A collapsed coordinate interval retains exact physical equality in the weak section order. -/
theorem closed_circle_section_lex_order
    (sectionData : S.ClosedBankCircleSection data.value data.center cutoff radius)
    {μ : ℝ} (nonnegative : 0 ≤ ε) (small_error : ε < 1 / 2)
    (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff) :
    (toLex ((data.value (S.lower.point sectionData.lowerHeight) - data.center).re,
      {S.lower.point sectionData.lowerHeight}) : ℝ ×ₗ Set ℂ) ≤
        toLex ((data.value (S.upper.point sectionData.upperHeight) - data.center).re,
          {S.upper.point sectionData.upperHeight}) := by
  have order := data.closed_circle_section_banks_ordered sectionData nonnegative small_error
    numerical linear_error margin radius_positive far
  apply Prod.Lex.toLex_le_toLex'.mpr
  refine ⟨order, ?_⟩
  intro equal
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have first := data.strict_quadrant_of_closed_margin close_margin margin sectionData.lower_closed
    (data.closed_circle_height_mem_Ioo radius_positive far sectionData.lower_closed
      sectionData.lower_radius).1
  have last := data.strict_quadrant_of_closed_margin close_margin margin sectionData.upper_closed
    (data.closed_circle_height_mem_Ioo radius_positive far sectionData.upper_closed
      sectionData.upper_radius).1
  have same_value := complex_eq_of_norm_re_eq
    (sectionData.lower_radius.trans sectionData.upper_radius.symm) equal first.2.le last.2.le
  exact Set.singleton_subset_singleton.mpr
    (data.closed_injective sectionData.lower_closed sectionData.upper_closed
      (sub_left_inj.mp same_value))

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
