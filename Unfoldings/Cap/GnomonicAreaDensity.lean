module

public import Unfoldings.Cap.SharpGnomonicSolidAngle
public import Unfoldings.Geometry.SphericalConvex

/-! Solid angle in a north-pole gnomonic chart is a weighted planar measure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped ENNReal Pointwise

/-- The cone below a gnomonic point has this maximum vertical coordinate in
the unit ball. -/
def gnomonicCeiling (g : Plane) : ℝ := ‖northLift g‖⁻¹

theorem gnomonicCeiling_pos (g : Plane) : 0 < gnomonicCeiling g :=
  inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero g))

theorem continuous_gnomonicCeiling : Continuous gnomonicCeiling :=
  continuous_northLift.norm.inv₀
    (fun g => norm_ne_zero_iff.mpr (northLift_ne_zero g))

private theorem lintegral_vertical_square {h : ℝ} (positive : 0 < h) :
    ∫⁻ t in Set.Ioo (0 : ℝ) h, ENNReal.ofReal (t ^ 2) = ENNReal.ofReal (h ^ 3 / 3) := by
  have integrable : IntegrableOn (fun t : ℝ => t ^ 2) (Set.Ioo 0 h) :=
    (continuous_id.pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal integrable
    (.of_forall (fun t : ℝ => sq_nonneg t)), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le positive.le, integral_pow]
  norm_num

/-- The cone of a compact gnomonic region has vertical sections equal to
scaled subsets of that same region, at the exact height of the sphere. -/
theorem solidAngle_gnomonic_eq_lintegral {s : Set Plane} (compact : IsCompact s) :
    solidAngleMeasure (gnomonicNormal '' s) =
      ∫⁻ g in s, ENNReal.ofReal (gnomonicCeiling g ^ 3) := by
  let split : Space ≃ᵐ Plane × ℝ :=
    verticalProduct.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Plane × ℝ)).symm
  have preserving : MeasurePreserving split :=
    verticalProduct.measurePreserving.trans (WithLp.volume_preserving_ofLp (U := Plane) (V := ℝ))
  let heights : Set (ℝ × Plane) := {p | p.2 ∈ s ∧ p.1 ∈ Set.Ioo 0 (gnomonicCeiling p.2)}
  have measured : MeasurableSet heights :=
    (compact.measurableSet.preimage measurable_snd).inter
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst (continuous_gnomonicCeiling.measurable.comp measurable_snd)))
  let slices : Set (Plane × ℝ) :=
    (fun p => (p.2, p.2⁻¹ • p.1)) ⁻¹' heights
  have measurable : MeasurableSet slices :=
    measured.preimage (measurable_snd.prodMk (measurable_snd.inv.smul measurable_fst))
  have unit : gnomonicNormal '' s ⊆ Metric.sphere (0 : Space) 1 := by
    rintro z ⟨g, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using gnomonicNormal_unit g
  have cover : Set.Ioo (0 : ℝ) 1 • (gnomonicNormal '' s) = split ⁻¹' slices := by
    ext z
    constructor
    · rintro ⟨r, r_mem, _, ⟨g, hg, rfl⟩, rfl⟩
      let t : ℝ := r * gnomonicCeiling g
      have tpos : 0 < t := mul_pos r_mem.1 (gnomonicCeiling_pos g)
      have tlt : t < gnomonicCeiling g := by
        exact mul_lt_of_lt_one_left (gnomonicCeiling_pos g) r_mem.2
      have height : (r • gnomonicNormal g) 2 = t := by
        change r * (‖northLift g‖⁻¹ * northLift g 2) = t
        rw [northLift_height, mul_one]
        rfl
      have trace : horizontal (r • gnomonicNormal g) = t • g := by
        rw [gnomonicNormal, NormedSpace.normalize, map_smul, map_smul, northLift_horizontal,
          smul_smul]
        rfl
      change ((r • gnomonicNormal g) 2)⁻¹ • horizontal (r • gnomonicNormal g) ∈ s ∧
        (r • gnomonicNormal g) 2 ∈ Set.Ioo 0
          (gnomonicCeiling (((r • gnomonicNormal g) 2)⁻¹ • horizontal (r • gnomonicNormal g)))
      rw [height, trace, smul_smul, inv_mul_cancel₀ tpos.ne', one_smul]
      exact ⟨hg, tpos, tlt⟩
    · intro member
      let t := z 2
      let g := t⁻¹ • horizontal z
      change g ∈ s ∧ t ∈ Set.Ioo 0 (gnomonicCeiling g) at member
      have position : z = t • northLift g := by
        apply verticalProduct.injective
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · change horizontal z = horizontal (t • northLift g)
          rw [map_smul, northLift_horizontal]
          change horizontal z = t • t⁻¹ • horizontal z
          rw [smul_smul, mul_inv_cancel₀ member.2.1.ne', one_smul]
        · change t = t * northLift g 2
          rw [northLift_height, mul_one]
      let r := t * ‖northLift g‖
      have normpos : 0 < ‖northLift g‖ := norm_pos_iff.mpr (northLift_ne_zero g)
      have rmem : r ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨mul_pos member.2.1 normpos, (lt_div_iff₀ normpos).mp (by simpa only [gnomonicCeiling, one_div] using member.2.2)⟩
      refine ⟨r, rmem, gnomonicNormal g, ⟨g, member.1, rfl⟩, ?_⟩
      change r • gnomonicNormal g = z
      rw [gnomonicNormal, NormedSpace.normalize, smul_smul]
      change (t * ‖northLift g‖ * ‖northLift g‖⁻¹) • northLift g = z
      rw [mul_assoc, mul_inv_cancel₀ normpos.ne', mul_one]
      exact position.symm
  let weight (t : ℝ) (g : Plane) : ℝ≥0∞ :=
    heights.indicator (fun p => ENNReal.ofReal (p.1 ^ 2)) (t, g)
  have weight_measurable : Measurable (Function.uncurry weight) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2)).indicator measured
  have section_integral (t : ℝ) :
      volume ((fun p : Plane => (p, t)) ⁻¹' slices) = ∫⁻ g, weight t g := by
    by_cases positive : 0 < t
    · let slice : Set Plane := {g | g ∈ s ∧ t ∈ Set.Ioo 0 (gnomonicCeiling g)}
      have section_measurable : MeasurableSet slice :=
        measured.preimage (measurable_const.prodMk measurable_id)
      have equal : (fun p : Plane => (p, t)) ⁻¹' slices = t • slice := by
        ext p
        change t⁻¹ • p ∈ slice ↔ p ∈ t • slice
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ positive.ne']
      rw [equal, Measure.addHaar_smul_of_nonneg volume positive.le,
        finrank_euclideanSpace, Fintype.card_fin]
      have integrand : weight t = slice.indicator (fun _ => ENNReal.ofReal (t ^ 2)) := by
        funext g
        by_cases hg : g ∈ slice
        · rw [Set.indicator_of_mem hg]
          exact Set.indicator_of_mem (show (t, g) ∈ heights from hg) _
        · rw [Set.indicator_of_notMem hg]
          exact Set.indicator_of_notMem (show (t, g) ∉ heights from hg) _
      rw [integrand, lintegral_indicator_const section_measurable, mul_comm]
    · have empty : (fun p : Plane => (p, t)) ⁻¹' slices = ∅ := by
        ext p
        exact iff_of_false (fun hp => positive (show t⁻¹ • p ∈ s ∧
          t ∈ Set.Ioo 0 (gnomonicCeiling (t⁻¹ • p)) from hp).2.1) (Set.notMem_empty p)
      rw [empty, measure_empty]
      have zero : weight t = 0 := funext (fun g =>
        Set.indicator_of_notMem (fun hg : (t, g) ∈ heights => positive hg.2.1) _)
      rw [zero]
      exact lintegral_zero_fun.symm
  have vertex_integral (g : Plane) :
      (∫⁻ t, weight t g) = s.indicator (fun g => ENNReal.ofReal (gnomonicCeiling g ^ 3 / 3)) g := by
    by_cases member : g ∈ s
    · rw [Set.indicator_of_mem member]
      have integrand : (fun t => weight t g) =
          (Set.Ioo (0 : ℝ) (gnomonicCeiling g)).indicator (fun t => ENNReal.ofReal (t ^ 2)) := by
        funext t
        by_cases ht : t ∈ Set.Ioo (0 : ℝ) (gnomonicCeiling g)
        · rw [Set.indicator_of_mem ht]
          exact Set.indicator_of_mem (show (t, g) ∈ heights from ⟨member, ht⟩) _
        · rw [Set.indicator_of_notMem ht]
          exact Set.indicator_of_notMem (fun pair : (t, g) ∈ heights => ht pair.2) _
      rw [integrand, lintegral_indicator measurableSet_Ioo]
      exact lintegral_vertical_square (gnomonicCeiling_pos g)
    · rw [Set.indicator_of_notMem member]
      have zero : (fun t => weight t g) = 0 := funext (fun t =>
        Set.indicator_of_notMem (fun pair : (t, g) ∈ heights => member pair.1) _)
      rw [zero]
      exact lintegral_zero_fun
  have volume_eq : volume (split ⁻¹' slices) =
      ∫⁻ g in s, ENNReal.ofReal (gnomonicCeiling g ^ 3 / 3) := by
    rw [preserving.measure_preimage measurable.nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_apply_symm measurable]
    calc
      _ = ∫⁻ t, ∫⁻ g, weight t g := lintegral_congr section_integral
      _ = ∫⁻ g, ∫⁻ t, weight t g := lintegral_lintegral_swap weight_measurable.aemeasurable
      _ = _ := by
        rw [← lintegral_indicator compact.measurableSet]
        exact lintegral_congr vertex_integral
  rw [solidAngleMeasure_apply (compact.image gnomonicNormal_lipschitz.continuous).measurableSet unit,
    cover, volume_eq, ← lintegral_const_mul _]
  swap
  · exact ENNReal.measurable_ofReal.comp ((continuous_gnomonicCeiling.pow 3).div_const 3).measurable
  apply lintegral_congr
  intro g
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ))]
  congr 1
  ring

end Unfoldings.Cap
