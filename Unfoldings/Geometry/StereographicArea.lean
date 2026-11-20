module

public import Unfoldings.Geometry.StereographicJacobian
public import Unfoldings.Geometry.SolidAngle
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Solid angle in the paper's stereographic chart, derived by spatial change of variables. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped ENNReal Pointwise

/-- Spherical area per unit of planar area in stereographic coordinates. -/
def stereographicDensity (x : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (4 / (1 + ‖x‖ ^ 2) ^ 2)

theorem continuous_inverseStereographic : Continuous inverseStereographic := by
  have lift : Continuous horizontalLift := horizontalLiftIsometry.continuous
  have den : Continuous (fun x : Plane => 1 + ‖x‖ ^ 2) :=
    continuous_const.add (continuous_id.norm.pow 2)
  unfold inverseStereographic
  exact ((continuous_const.div den (fun _ => by positivity)).smul lift).add
    (((continuous_const.sub (continuous_id.norm.pow 2)).div den
      (fun _ => by positivity)).smul continuous_const)

private theorem lintegral_radial_sq :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ 2)) = ENNReal.ofReal (1 / 3) := by
  have continuous : Continuous (fun t : ℝ => t ^ 2) := continuous_id.pow _
  have h : IntegrableOn (fun t : ℝ => t ^ 2) (Set.Ioo 0 1) volume :=
    (continuous.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall (fun t => sq_nonneg t)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  norm_num

/-- The exact area formula for a compact planar region in the chart. -/
theorem solidAngle_inverseStereographic_image {s : Set Plane} (compact : IsCompact s) :
    solidAngleMeasure (inverseStereographic '' s) = ∫⁻ x in s, stereographicDensity x := by
  let p : Set Space := {z | horizontal z ∈ s ∧ z 2 ∈ Set.Ioo (0 : ℝ) 1}
  let split : Space ≃ᵐ Plane × ℝ := verticalProduct.toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Plane × ℝ)).symm
  have preserving : MeasurePreserving split :=
    verticalProduct.measurePreserving.trans (WithLp.volume_preserving_ofLp (U := Plane) (V := ℝ))
  have preimage : p = split ⁻¹' (s ×ˢ Set.Ioo (0 : ℝ) 1) := rfl
  have measurable : MeasurableSet p :=
    preimage ▸ (compact.measurableSet.prod measurableSet_Ioo).preimage split.measurable
  have image : radialStereographic '' p =
      Set.Ioo (0 : ℝ) (1 : ℝ) • (inverseStereographic '' s) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w 2, hw.2, inverseStereographic (horizontal w), ⟨horizontal w, hw.1, rfl⟩, rfl⟩
    · rintro ⟨t, ht, _, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨horizontalAtHeight x t, ?_, ?_⟩
      · exact ⟨by simpa using hx, by simpa using ht⟩
      · simp only [radialStereographic, horizontal_horizontalAtHeight, height_horizontalAtHeight]
  have injective : Set.InjOn radialStereographic p := by
    intro z hz w hw same
    have scale (v : Space) (hv : v ∈ p) : ‖radialStereographic v‖ = v 2 := by
      rw [radialStereographic, norm_smul, inverseStereographic_unit, mul_one,
        Real.norm_of_nonneg hv.2.1.le]
    have height := (scale z hz).symm.trans ((congrArg norm same).trans (scale w hw))
    have sameChart : inverseStereographic (horizontal z) = inverseStereographic (horizontal w) := by
      rw [radialStereographic, radialStereographic, ← height] at same
      exact smul_right_injective Space hz.2.1.ne' same
    apply split.injective
    change (horizontal z, z 2) = (horizontal w, w 2)
    exact Prod.ext
      (by simpa only [stereographicCoord_inverseStereographic] using
        congrArg stereographicCoord sameChart) height
  have unit : inverseStereographic '' s ⊆ Metric.sphere (0 : Space) 1 := by
    rintro _ ⟨x, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using inverseStereographic_unit x
  rw [solidAngleMeasure_apply (compact.image continuous_inverseStereographic).measurableSet unit,
    ← image]
  have jac := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure Space) measurable
    (fun z _ => (hasFDerivAt_radialStereographic z).hasFDerivWithinAt) injective (fun _ => 1)
  have nonnegative (z : Space) : 0 ≤ 4 * (z 2) ^ 2 / (1 + ‖horizontal z‖ ^ 2) ^ 2 :=
    by positivity
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul, mul_one,
    det_radialStereographicDerivative, abs_of_nonneg (nonnegative _)] at jac
  rw [jac, preimage]
  let f (x : Plane × ℝ) := stereographicDensity x.1 * ENNReal.ofReal (x.2 ^ 2)
  have eq (z : Space) : ENNReal.ofReal (4 * (z 2) ^ 2 / (1 + ‖horizontal z‖ ^ 2) ^ 2) =
      f (split z) := by
    change _ = ENNReal.ofReal (4 / (1 + ‖horizontal z‖ ^ 2) ^ 2) * ENNReal.ofReal ((z 2) ^ 2)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [eq]
  rw [preserving.setLIntegral_comp_preimage_emb split.measurableEmbedding f,
    Measure.volume_eq_prod]
  have densityDen : Continuous (fun x : Plane => (1 + ‖x‖ ^ 2) ^ 2) :=
    (continuous_const.add (continuous_id.norm.pow 2)).pow 2
  have densityMeas : Measurable stereographicDensity :=
    (continuous_const.div densityDen
      (fun x => show (1 + ‖x‖ ^ 2) ^ 2 ≠ 0 by positivity)).measurable.ennreal_ofReal
  have sqMeas : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ 2)) :=
    (continuous_id.pow 2).measurable.ennreal_ofReal
  have fMeas : Measurable f :=
    (densityMeas.comp measurable_fst).mul (sqMeas.comp measurable_snd)
  rw [setLIntegral_prod f fMeas.aemeasurable]
  have radial (x : Plane) :
      (∫⁻ t in Set.Ioo (0 : ℝ) 1, f (x, t)) =
        stereographicDensity x * ENNReal.ofReal (1 / 3) := by
    dsimp [f]
    rw [lintegral_const_mul _ sqMeas, lintegral_radial_sq]
  simp_rw [radial]
  rw [lintegral_mul_const _ densityMeas]
  have third : (3 : ℝ≥0∞) * ENNReal.ofReal (1 / 3) = 1 := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [mul_left_comm, third, mul_one]

end Unfoldings.Cap
