module

public import Unfoldings.Cap.VerticalProduct
public import Unfoldings.Geometry.SolidAngle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The north spherical cap has the sharp solid-angle bound from its volume slices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory Real
open scoped ENNReal Pointwise

private def radialSliceRegion (a b : ℝ) (radius : ℝ → ℝ) : Set Space :=
  {z | z 2 ∈ Set.Icc a b ∧ ‖horizontal z‖ ≤ radius (z 2)}

private theorem volume_radialSliceRegion (a b : ℝ) (order : a ≤ b)
    (radius : ℝ → ℝ) (continuous : Continuous radius)
    (nonnegative : ∀ t ∈ Set.Icc a b, 0 ≤ radius t) :
    volume (radialSliceRegion a b radius) =
      ENNReal.ofReal (∫ t in a..b, π * radius t ^ 2) := by
  let split : Space ≃ᵐ Plane × ℝ :=
    verticalProduct.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Plane × ℝ)).symm
  have preserving : MeasurePreserving split :=
    verticalProduct.measurePreserving.trans (WithLp.volume_preserving_ofLp (U := Plane) (V := ℝ))
  let slices : Set (Plane × ℝ) := {pt | pt.2 ∈ Set.Icc a b ∧ ‖pt.1‖ ≤ radius pt.2}
  have measurable : MeasurableSet slices := measurableSet_Icc.preimage measurable_snd |>.inter
    (measurableSet_le (continuous_norm.comp continuous_fst).measurable
      (continuous.comp continuous_snd).measurable)
  change volume (split ⁻¹' slices) = _
  rw [preserving.measure_preimage measurable.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm measurable]
  calc
    _ = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (π * radius t ^ 2) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Icc a b
      · rw [Set.indicator_of_mem ht]
        have section_eq : (fun p : Plane => (p, t)) ⁻¹' slices =
            Metric.closedBall (0 : Plane) (radius t) := by
          ext p
          simp only [Set.mem_preimage, slices, Set.mem_ofPred_eq, ht, true_and,
            Metric.mem_closedBall, dist_zero_right]
        rw [section_eq, EuclideanSpace.volume_closedBall_fin_two,
          ← ENNReal.ofReal_pow (nonnegative t ht), ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
      · rw [Set.indicator_of_notMem ht]
        have section_eq : (fun p : Plane => (p, t)) ⁻¹' slices = ∅ := by
          ext p
          simp only [Set.mem_preimage, slices, Set.mem_ofPred_eq, ht, false_and, Set.notMem_empty]
        rw [section_eq, measure_empty]
    _ = ENNReal.ofReal (∫ t in a..b, π * radius t ^ 2) := by
      have cint : Continuous (fun t => π * radius t ^ 2) := by fun_prop
      rw [← ofReal_integral_eq_lintegral_ofReal (cint.integrableOn_Icc)
        (.of_forall (fun t => mul_nonneg pi_pos.le (sq_nonneg _))),
        integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le order]

/-- Sharp area bound for unit directions at or above a positive north height. -/
theorem solidAngleMeasure_north_cap_le {c : ℝ} (positive : 0 < c) (c_le : c ≤ 1) :
    solidAngleMeasure {z : Space | z ∈ Metric.sphere 0 1 ∧ c ≤ z 2} ≤
      ENNReal.ofReal (2 * π * (1 - c)) := by
  let S : Set Space := {z | z ∈ Metric.sphere 0 1 ∧ c ≤ z 2}
  have closed : IsClosed S := Metric.isClosed_sphere.inter (isClosed_le continuous_const
    (EuclideanSpace.proj 2).continuous)
  let r := sqrt (1 - c ^ 2) / c
  have cs : 0 ≤ 1 - c ^ 2 := by
    exact sub_nonneg.mpr (by simpa only [one_pow] using pow_le_pow_left₀ positive.le c_le 2)
  have rn : 0 ≤ r := div_nonneg (sqrt_nonneg _) positive.le
  let lower := radialSliceRegion 0 c (fun t => r * t)
  let upper := radialSliceRegion c 1 (fun t => sqrt (1 - t ^ 2))
  have cover : Set.Ioo (0 : ℝ) 1 • S ⊆ lower ∪ upper := by
    rintro z ⟨ρ, hρ, n, hn, rfl⟩
    have n_norm : ‖n‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hn.1
    have height_lower : c ≤ n 2 := hn.2
    have nh_pos := positive.trans_le height_lower
    have h_unit := horizontal_norm_sq n
    rw [n_norm, one_pow] at h_unit
    have z_norm : ‖ρ • n‖ = ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ.1, n_norm, mul_one]
    have h_z := horizontal_norm_sq (ρ • n)
    rw [z_norm] at h_z
    have z_pos : 0 < (ρ • n) 2 := mul_pos hρ.1 nh_pos
    have z_le : (ρ • n) 2 ≤ 1 := by
      have sq : (ρ • n) 2 ^ 2 ≤ (1 : ℝ) := by
        have r_sq : ρ ^ 2 ≤ (1 : ℝ) := by
          simpa only [one_pow] using pow_le_pow_left₀ hρ.1.le hρ.2.le 2
        linarith only [r_sq, h_z, sq_nonneg ‖horizontal (ρ • n)‖]
      exact (sq_le_sq₀ z_pos.le zero_le_one).mp (by rwa [one_pow])
    by_cases low : (ρ • n) 2 ≤ c
    · refine Or.inl ⟨⟨z_pos.le, low⟩, ?_⟩
      have circle : c * ‖horizontal n‖ ≤ sqrt (1 - c ^ 2) * n 2 := by
        apply (sq_le_sq₀ (by positivity) (mul_nonneg (sqrt_nonneg _) nh_pos.le)).mp
        rw [mul_pow, mul_pow, sq_sqrt cs]
        have height_sq := pow_le_pow_left₀ positive.le height_lower 2
        nlinarith only [height_sq, h_unit, (congrArg (fun t : ℝ => c ^ 2 * t) h_unit)]
      have slope : ‖horizontal n‖ ≤ r * n 2 := by
        dsimp [r]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ positive).mpr
        simpa only [mul_comm ‖horizontal n‖ c] using circle
      change ‖horizontal (ρ • n)‖ ≤ r * (ρ * n 2)
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hρ.1, mul_left_comm r]
      exact mul_le_mul_of_nonneg_left slope hρ.1.le
    · refine Or.inr ⟨⟨le_of_not_ge low, z_le⟩, ?_⟩
      apply (le_sqrt (norm_nonneg _) _).mpr
      · nlinarith only [h_z, sq_nonneg ‖horizontal (ρ • n)‖,
          (pow_le_pow_left₀ hρ.1.le hρ.2.le 2)]
      · nlinarith only [(pow_le_pow_left₀ z_pos.le z_le 2)]
  change solidAngleMeasure S ≤ _
  rw [solidAngleMeasure_apply closed.measurableSet (fun _ h => h.1)]
  have lo := volume_radialSliceRegion 0 c positive.le (fun t => r * t) (by fun_prop)
    (fun t ht => mul_nonneg rn ht.1)
  have hi := volume_radialSliceRegion c 1 c_le (fun t => sqrt (1 - t ^ 2)) (by fun_prop)
    (fun t _ => sqrt_nonneg _)
  have r_sq : r ^ 2 = (1 - c ^ 2) / c ^ 2 := by rw [div_pow, sq_sqrt cs]
  have il : (∫ t in (0 : ℝ)..c, π * (r * t) ^ 2) = π * (1 - c ^ 2) * c / 3 := by
    simp_rw [mul_pow, ← mul_assoc, intervalIntegral.integral_const_mul, integral_pow]
    rw [r_sq]
    field_simp [positive.ne']
    ring
  have iu : (∫ t in c..(1 : ℝ), π * sqrt (1 - t ^ 2) ^ 2) =
      π * (2 / 3 - c + c ^ 3 / 3) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    calc
      _ = ∫ t in c..(1 : ℝ), 1 - t ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le c_le] at ht
        exact sq_sqrt (by nlinarith only [(pow_le_pow_left₀ (positive.le.trans ht.1) ht.2 2)])
      _ = _ := by
        have one : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume c 1 :=
          continuous_const.intervalIntegrable _ _
        have square : IntervalIntegrable (fun t : ℝ => t ^ 2) volume c 1 :=
          (continuous_id.pow 2).intervalIntegrable _ _
        rw [intervalIntegral.integral_sub one square, intervalIntegral.integral_const, integral_pow]
        norm_num
        ring
  have lnon : 0 ≤ π * (1 - c ^ 2) * c / 3 := by positivity
  have unon : 0 ≤ π * (2 / 3 - c + c ^ 3 / 3) := by
    rw [← iu]
    exact intervalIntegral.integral_nonneg c_le (fun t _ => mul_nonneg pi_pos.le (sq_nonneg _))
  calc
    _ ≤ 3 * (volume lower + volume upper) :=
      mul_le_mul_of_nonneg_left ((measure_mono cover).trans (measure_union_le lower upper))
        (by positivity)
    _ = ENNReal.ofReal (2 * π * (1 - c)) := by
      rw [lo, hi, il, iu, ← ENNReal.ofReal_add lnon unon,
        show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

end Unfoldings.Cap
