module

public import Unfoldings.FewestNets.LatitudeTriangleSelector
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Horizontal slices compute the exact area of the three-exit chart triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory Real
open scoped ENNReal

/-- Integrating the linear horizontal section width gives half the base times the altitude. -/
theorem volume_latitudeSlopeTriangle {left right base apex height : ℝ}
    (base_order : left ≤ right) (height_pos : 0 < height) :
    volume (latitudeSlopeTriangle left right base apex height) =
      ENNReal.ofReal ((right - left) * height / 2) := by
  let t (v : ℝ) := (base - v) / height
  let lo (v : ℝ) := (1 - t v) * left + t v * apex
  let hi (v : ℝ) := (1 - t v) * right + t v * apex
  let slices : Set (ℝ × ℝ) :=
    {z | z.2 ∈ Set.Icc (base - height) base ∧ z.1 ∈ Set.Icc (lo z.2) (hi z.2)}
  have measurable : MeasurableSet slices := by
    have lower : Measurable (fun z : ℝ × ℝ => lo z.2) := by dsimp [lo, t]; fun_prop
    have upper : Measurable (fun z : ℝ × ℝ => hi z.2) := by dsimp [hi, t]; fun_prop
    exact (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_le lower measurable_fst).inter (measurableSet_le measurable_fst upper))
  let chart := (exitHeadingChart false).toMeasurableEquiv.trans Complex.measurableEquivRealProd
  have preserving : MeasurePreserving chart :=
    (exitHeadingChart false).measurePreserving.trans Complex.volume_preserving_equiv_real_prod
  have shape : latitudeSlopeTriangle left right base apex height = chart ⁻¹' slices := by
    ext p
    unfold latitudeSlopeTriangle
    rw [Set.mem_preimage, mem_parameter_triangle_iff base_order]
    let z := exitHeadingChart false p
    change (∃ u ∈ Set.Icc (0 : ℝ) 1,
      z.im = (1 - u) * base + u * (base - height) ∧
      z.re ∈ Set.Icc ((1 - u) * left + u * apex) ((1 - u) * right + u * apex)) ↔
      z.im ∈ Set.Icc (base - height) base ∧ z.re ∈ Set.Icc (lo z.im) (hi z.im)
    constructor
    · rintro ⟨u, hu, at_y, at_x⟩
      have linear : z.im = base - u * height := by rw [at_y]; ring
      have value : t z.im = u := by
        apply (div_eq_iff height_pos.ne').mpr
        linarith only [linear]
      refine ⟨?_, by simpa only [lo, hi, value] using at_x⟩
      constructor
      · linarith only [linear, mul_le_mul_of_nonneg_right hu.2 height_pos.le]
      · linarith only [linear, mul_nonneg hu.1 height_pos.le]
    · rintro ⟨hy, hx⟩
      refine ⟨t z.im, ⟨div_nonneg (sub_nonneg.mpr hy.2) height_pos.le, ?_⟩, ?_, hx⟩
      · exact (div_le_one height_pos).mpr (by linarith only [hy.1])
      · have scale : t z.im * height = base - z.im :=
          div_mul_cancel₀ _ height_pos.ne'
        linarith only [scale]
  rw [shape, preserving.measure_preimage measurable.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm measurable]
  have t_le (v : ℝ) (hv : v ∈ Set.Icc (base - height) base) : t v ≤ 1 :=
    (div_le_one height_pos).mpr (by linarith only [hv.1])
  calc
    _ = ∫⁻ v in Set.Icc (base - height) base,
        ENNReal.ofReal ((1 - t v) * (right - left)) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro v
      by_cases hv : v ∈ Set.Icc (base - height) base
      · rw [Set.indicator_of_mem hv]
        have section_eq : (fun x : ℝ => (x, v)) ⁻¹' slices = Set.Icc (lo v) (hi v) := by
          ext x
          exact and_iff_right hv
        rw [section_eq, Real.volume_Icc]
        congr 1
        dsimp [hi, lo]
        ring
      · rw [Set.indicator_of_notMem hv]
        have section_eq : (fun x : ℝ => (x, v)) ⁻¹' slices = ∅ := by
          ext x
          exact iff_of_false (fun h => hv h.1) (Set.notMem_empty x)
        rw [section_eq, measure_empty]
    _ = _ := by
      have integrable : IntegrableOn (fun v => (1 - t v) * (right - left))
          (Set.Icc (base - height) base) := by
        apply Continuous.integrableOn_Icc
        dsimp [t]
        fun_prop
      have nonneg : ∀ᵐ v ∂volume.restrict (Set.Icc (base - height) base),
          0 ≤ (1 - t v) * (right - left) :=
        (ae_restrict_mem measurableSet_Icc).mono (fun v hv =>
          mul_nonneg (sub_nonneg.mpr (t_le v hv)) (sub_nonneg.mpr base_order))
      rw [← ofReal_integral_eq_lintegral_ofReal integrable nonneg, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show base - height ≤ base by linarith)]
      congr 1
      have integrand : (fun v => (1 - t v) * (right - left)) =
          fun v => (right - left) / height * (v - (base - height)) := by
        funext v
        dsimp only [t]
        field_simp [height_pos.ne']
        ring
      have linear : IntervalIntegrable (fun v : ℝ => v) volume (base - height) base :=
        continuous_id.intervalIntegrable _ _
      rw [integrand, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        linear (continuous_const.intervalIntegrable _ _),
        integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [height_pos.ne']
      ring

end Unfoldings.FewestNets
