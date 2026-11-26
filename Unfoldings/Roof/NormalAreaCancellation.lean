module

public import Unfoldings.Convex.SegmentProgress
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Active slopes identify the signs of curvature and transport relative to the normal trace. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

/-- Along a horizontal link, the horizontal coordinates of its active slopes advance monotonically. -/
theorem active_firstCoord_le {x y p q : Plane} (first : E.Active x p) (last : E.Active y q)
    (level : x 1 = y 1) (advance : x 0 < y 0) :
    p 0 ≤ q 0 := by
  have h := E.active_monotone first last
  change 0 ≤ inner ℝ (q - p) (y - x) at h
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at h
  change 0 ≤ (q 0 - p 0) * (y 0 - x 0) + (q 1 - p 1) * (y 1 - x 1) at h
  rw [level, sub_self, mul_zero, add_zero] at h
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left h (sub_pos.mpr advance))

/-- At a fixed horizontal slope, a point above the link has a slope on or
above its normal trace. The horizontal coordinates of the contact points are unrestricted. -/
theorem active_secondCoord_le {x y p q : Plane} (first : E.Active x p) (last : E.Active y q)
    (same_slope : p 0 = q 0) (above : x 1 < y 1) :
    p 1 ≤ q 1 := by
  have h := E.active_monotone first last
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at h
  change 0 ≤ (q 0 - p 0) * (y 0 - x 0) + (q 1 - p 1) * (y 1 - x 1) at h
  rw [same_slope, sub_self, zero_mul, zero_add] at h
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left h (sub_pos.mpr above))

end Unfoldings.SlopeEnvelope

namespace Unfoldings

open MeasureTheory
open scoped ENNReal

/-- If the curvature and transport densities have the same sign at their
common support, their difference costs at most one copy of the support's area. -/
theorem abs_integral_sub_le_measure_of_same_sign {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {cell : Set X} (measurable_cell : MeasurableSet cell)
    (finite : μ cell < ∞) {curvature transport : X → ℝ}
    (curvature_integrable : Integrable curvature μ) (transport_integrable : Integrable transport μ)
    (bounded : ∀ᵐ x ∂μ, |curvature x| ≤ 1 ∧ |transport x| ≤ 1 ∧ 0 ≤ curvature x * transport x)
    (supported : ∀ᵐ x ∂μ, x ∉ cell → curvature x = 0 ∧ transport x = 0) :
    |(∫ x, curvature x ∂μ) - (∫ x, transport x ∂μ)| ≤ μ.real cell := by
  rw [← integral_sub curvature_integrable transport_integrable]
  have pointwise : ∀ᵐ x ∂μ, ‖curvature x - transport x‖ ≤ cell.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [bounded, supported] with x bound support
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ cell
    · rw [Set.indicator_of_mem hx, abs_le]
      obtain ⟨a, b, agree⟩ := bound
      rw [abs_le] at a b
      rcases mul_nonneg_iff.mp agree with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        constructor <;> linarith
    · rw [Set.indicator_of_notMem hx, (support hx).1, (support hx).2, sub_self, abs_zero]
  have total : (μ.restrict cell) Set.univ = μ cell := by
    rw [Measure.restrict_apply_univ]
  let : IsFiniteMeasure (μ.restrict cell) := ⟨total.symm ▸ finite⟩
  have integrable_bound : Integrable (cell.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurable_cell).mpr (integrable_const _)

  calc
    _ ≤ ∫ x, ‖curvature x - transport x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, cell.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono_ae (curvature_integrable.sub transport_integrable).norm integrable_bound pointwise
    _ = μ.real cell := by
      rw [integral_indicator measurable_cell, integral_const, smul_eq_mul, mul_one, Measure.real, total]
      rfl

end Unfoldings
