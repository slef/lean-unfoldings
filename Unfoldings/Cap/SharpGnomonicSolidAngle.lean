module

public import Unfoldings.Cap.ConicalArea
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Vertical slices give a sharp planar-area upper bound for solid angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped ENNReal Pointwise

/-- The solid angle of the inverse gnomonic image is at most the planar volume.
At height `t` in the unit ball, its horizontal section is contained in `t • s`. -/
theorem solidAngle_gnomonic_le_volume {s : Set Plane} (compact : IsCompact s) :
    solidAngleMeasure (gnomonicNormal '' s) ≤ volume s := by
  let split : Space ≃ᵐ Plane × ℝ :=
    verticalProduct.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Plane × ℝ)).symm
  have preserving : MeasurePreserving split :=
    verticalProduct.measurePreserving.trans (WithLp.volume_preserving_ofLp (U := Plane) (V := ℝ))
  let slices : Set (Plane × ℝ) :=
    {pt | pt.2 ∈ Set.Ioo 0 1 ∧ pt.2⁻¹ • pt.1 ∈ s}
  have measurable : MeasurableSet slices := (measurableSet_Ioo.preimage measurable_snd).inter
    (compact.measurableSet.preimage (measurable_snd.inv.smul measurable_fst))
  have unit : gnomonicNormal '' s ⊆ Metric.sphere (0 : Space) 1 := by
    rintro z ⟨g, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using gnomonicNormal_unit g
  have cover : Set.Ioo (0 : ℝ) 1 • (gnomonicNormal '' s) ⊆ split ⁻¹' slices := by
    rintro z ⟨ρ, ρ_mem, _, ⟨g, hg, rfl⟩, rfl⟩
    let t : ℝ := ρ * ‖northLift g‖⁻¹
    have norm_pos : 0 < ‖northLift g‖ := norm_pos_iff.mpr (northLift_ne_zero g)
    have t_pos : 0 < t := mul_pos ρ_mem.1 (inv_pos.mpr norm_pos)
    have t_small : t < 1 := by
      change ρ * ‖northLift g‖⁻¹ < 1
      rw [← div_eq_mul_inv]
      exact (div_lt_one norm_pos).mpr (ρ_mem.2.trans_le (northLift_norm_lower g))
    change (ρ • gnomonicNormal g) 2 ∈ Set.Ioo 0 1 ∧
      ((ρ • gnomonicNormal g) 2)⁻¹ • horizontal (ρ • gnomonicNormal g) ∈ s
    have h : (ρ • gnomonicNormal g) 2 = t := by
      change ρ * (‖northLift g‖⁻¹ * northLift g 2) = t
      rw [northLift_height, mul_one]
    have p : horizontal (ρ • gnomonicNormal g) = t • g := by
      rw [gnomonicNormal, NormedSpace.normalize, map_smul, map_smul, northLift_horizontal,
        smul_smul]
    rw [h, p, smul_smul, inv_mul_cancel₀ t_pos.ne', one_smul]
    exact ⟨⟨t_pos, t_small⟩, hg⟩
  have scaled_volume : volume (split ⁻¹' slices) = ENNReal.ofReal (1 / 3 : ℝ) * volume s := by
    rw [preserving.measure_preimage measurable.nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_apply_symm measurable]
    calc
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ 2) * volume s := by
        rw [← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
        · rw [Set.indicator_of_mem ht]
          have section_eq : (fun p : Plane => (p, t)) ⁻¹' slices = t • s := by
            ext p
            change (t ∈ Set.Ioo (0 : ℝ) 1 ∧ t⁻¹ • p ∈ s) ↔ p ∈ t • s
            rw [and_iff_right ht, Set.mem_smul_set_iff_inv_smul_mem₀ ht.1.ne']
          rw [section_eq, Measure.addHaar_smul_of_nonneg volume ht.1.le,
            finrank_euclideanSpace, Fintype.card_fin]
        · rw [Set.indicator_of_notMem ht]
          have empty : (fun p : Plane => (p, t)) ⁻¹' slices = ∅ := by
            ext p
            exact iff_of_false (fun hp => ht hp.1) (Set.notMem_empty p)
          rw [empty, measure_empty]
      _ = _ := by
        rw [lintegral_mul_const _ (by fun_prop)]
        congr 1
        have integrable : IntegrableOn (fun t : ℝ => t ^ 2) (Set.Ioo 0 1) :=
          (continuous_id.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal integrable
          (.of_forall (fun t : ℝ => sq_nonneg t)), ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
        norm_num
  rw [solidAngleMeasure_apply
    (compact.image gnomonicNormal_lipschitz.continuous).measurableSet unit]
  calc
    _ ≤ 3 * volume (split ⁻¹' slices) := mul_le_mul_of_nonneg_left (measure_mono cover) (by positivity)
    _ = volume s := by
      rw [scaled_volume, ← mul_assoc,
        show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num

end Unfoldings.Cap
