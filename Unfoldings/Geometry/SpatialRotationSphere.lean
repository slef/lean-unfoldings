module

public import Unfoldings.Geometry.SpatialRotationAction
public import Unfoldings.Geometry.SolidAngleSymmetry

/-! A Haar-rotated unit vector is uniform with respect to the actual solid-angle measure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open MeasureTheory
open scoped ENNReal

/-- Uniform probability on the unit sphere, using ambient coordinates. -/
def uniformSphere : Measure Space :=
  (ENNReal.ofReal (4 * Real.pi))⁻¹ • solidAngleMeasure

instance : IsProbabilityMeasure uniformSphere := by
  constructor
  rw [uniformSphere, Measure.smul_apply, solidAngleMeasure_univ]
  change (ENNReal.ofReal (4 * Real.pi))⁻¹ * (ENNReal.ofReal (4 * Real.pi)) = 1
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem uniformSphere_ae_norm_one : ∀ᵐ x ∂uniformSphere, ‖x‖ = 1 := by
  rw [ae_iff]
  change uniformSphere {x : Space | ‖x‖ ≠ 1} = 0
  rw [show {x : Space | ‖x‖ ≠ 1} = (Metric.sphere (0 : Space) 1)ᶜ by
    ext x; simp]
  rw [uniformSphere, Measure.smul_apply, solidAngleMeasure_off_sphere, smul_zero]

theorem uniformSphere_preimage_linear (g : SpatialRotation) {S : Set Space}
    (measurable : MeasurableSet S) : uniformSphere (linear g ⁻¹' S) = uniformSphere S := by
  simp only [uniformSphere, Measure.smul_apply]
  congr 1
  exact (solidAngleMeasure_preserving (isometry g)).measure_preimage measurable.nullMeasurableSet

/-- The pushforward of rotation probability by evaluation at any unit vector
is normalized solid angle. The proof averages the invariant law over a
transitive rotation action. -/
theorem map_linear_probability {v : Space} (unit : ‖v‖ = 1) :
    probability.map (fun g => linear g v) = uniformSphere := by
  ext S hS
  have evaluation : Measurable (fun g : SpatialRotation => linear g v) :=
    (continuous_apply.comp (continuous_id.prodMk continuous_const)).measurable
  let flag : Space → ℝ≥0∞ := S.indicator (fun _ => 1)
  have measurable_flag : Measurable flag := measurable_const.indicator hS
  have flag_integral (μ : Measure Space) : (∫⁻ x, flag x ∂μ) = μ S := by
    simp only [flag, lintegral_indicator hS, lintegral_const, Measure.restrict_apply_univ, one_mul]
  have joint : Measurable (fun z : SpatialRotation × Space => flag (linear z.1 z.2)) :=
    measurable_flag.comp continuous_apply.measurable
  have orbit (x : Space) (norm : ‖x‖ = 1) :
      (∫⁻ g, flag (linear g x) ∂probability) = ∫⁻ g, flag (linear g v) ∂probability := by
    obtain ⟨r, hr⟩ := exists_linear_apply_eq_of_norm_eq (unit.trans norm.symm)
    simp only [← hr, ← LinearMap.comp_apply, ← linear_mul]
    exact lintegral_mul_right_eq_self (μ := probability) (fun g => flag (linear g v)) r
  calc
    probability.map (fun g => linear g v) S =
        ∫⁻ g, flag (linear g v) ∂probability := by
      rw [← lintegral_map measurable_flag evaluation, flag_integral]
    _ = ∫⁻ x, ∫⁻ g, flag (linear g x) ∂probability ∂uniformSphere := by
      rw [lintegral_congr_ae (uniformSphere_ae_norm_one.mono orbit), lintegral_const,
        measure_univ, mul_one]
    _ = ∫⁻ g, ∫⁻ x, flag (linear g x) ∂uniformSphere ∂probability :=
      (lintegral_lintegral_swap joint.aemeasurable).symm
    _ = uniformSphere S := by
      have integral (g : SpatialRotation) : (∫⁻ x, flag (linear g x) ∂uniformSphere) =
          uniformSphere S := by
        change (∫⁻ x, flag (isometry g x) ∂uniformSphere) = uniformSphere S
        rw [← lintegral_map measurable_flag (isometry g).continuous.measurable, flag_integral,
          Measure.map_apply (isometry g).continuous.measurable hS]
        exact uniformSphere_preimage_linear g hS
      simp only [integral, lintegral_const, measure_univ, mul_one]

/-- A rotated unit direction lies on any fixed genuine great circle with probability zero. -/
theorem probability_linear_hyperplane {v : Space} (unit : ‖v‖ = 1)
    (normal : Space →L[ℝ] ℝ) (nonzero : normal ≠ 0) :
    probability {g | normal (linear g v) = 0} = 0 := by
  have evaluation : Measurable (fun g : SpatialRotation => linear g v) :=
    (continuous_apply.comp (continuous_id.prodMk continuous_const)).measurable
  have h : MeasurableSet {x : Space | normal x = 0} :=
    (isClosed_eq normal.continuous continuous_const).measurableSet
  change probability ((fun g => linear g v) ⁻¹' {x | normal x = 0}) = 0
  rw [← Measure.map_apply evaluation h, map_linear_probability unit, uniformSphere,
    Measure.smul_apply, solidAngleMeasure_ker normal nonzero, smul_zero]

/-- One random rotation avoids every boundary great circle for every
direction in a finite family, almost surely. -/
theorem ae_avoids_finite_hyperplanes {I J : Type*} [Finite I] [Finite J]
    (ray : I → Space) (unit : ∀ i, ‖ray i‖ = 1)
    (normal : J → Space →L[ℝ] ℝ) (nonzero : ∀ j, normal j ≠ 0) :
    ∀ᵐ g ∂probability, ∀ i j, normal j (linear g (ray i)) ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  simpa only [ae_iff, not_not] using probability_linear_hyperplane (unit i) (normal j) (nonzero j)

end Unfoldings.SpatialRotation
