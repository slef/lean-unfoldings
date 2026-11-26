module

public import Unfoldings.Cap.GnomonicAreaDensity
public import Unfoldings.Geometry.GnomonicRibbonIntegral

/-! The same solid-angle measure on ordinary Cartesian products. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory Real
open scoped ENNReal

/-- The two Cartesian coordinates of the tangent chart. -/
def planeCartesian : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem planeCartesian_preserving : MeasurePreserving planeCartesian volume (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  exact (volume_preserving_finTwoArrow ℝ).comp
    ((PiLp.volume_preserving_toLp (Fin 2)).symm (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

@[simp] theorem planeCartesian_apply (g : Plane) : planeCartesian g = (g 0, g 1) := rfl

theorem cartesianGnomonicDensity_nonneg (z : ℝ × ℝ) : 0 ≤ cartesianGnomonicDensity z := by
  unfold cartesianGnomonicDensity
  positivity

/-- The Cartesian density is precisely the cube of the ceiling in the cone computation. -/
theorem cartesianGnomonicDensity_plane (g : Plane) :
    cartesianGnomonicDensity (planeCartesian g) = gnomonicCeiling g ^ 3 := by
  have square : ‖northLift g‖ ^ 2 = 1 + g 0 ^ 2 + g 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change g 0 ^ 2 + g 1 ^ 2 + (1 : ℝ) ^ 2 = _
    ring
  have norm_eq : ‖northLift g‖ = √(1 + g 0 ^ 2 + g 1 ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp
    rw [square, sq_sqrt (by positivity)]
  rw [cartesianGnomonicDensity, planeCartesian_apply, gnomonicCeiling, norm_eq, inv_pow, one_div]

/-- The same measure in the usual horizontal and vertical product coordinates. -/
def cartesianSolidAngle : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity (fun z => ENNReal.ofReal (cartesianGnomonicDensity z))

/-- The Cartesian product measure computes the actual solid angle of a compact
normal region in the upper hemisphere. -/
theorem cartesianSolidAngle_image {s : Set Plane} (compact : IsCompact s) :
    cartesianSolidAngle (planeCartesian '' s) = solidAngleMeasure (gnomonicNormal '' s) := by
  rw [cartesianSolidAngle, withDensity_apply (fun z => ENNReal.ofReal (cartesianGnomonicDensity z)) (planeCartesian.measurableSet_image.mpr compact.measurableSet),
    solidAngle_gnomonic_eq_lintegral compact]
  have transport := planeCartesian_preserving.restrict_preimage_emb
    planeCartesian.measurableEmbedding (planeCartesian '' s)
  rw [Set.preimage_image_eq _ planeCartesian.injective] at transport
  rw [← transport.lintegral_comp_emb planeCartesian.measurableEmbedding
    (fun z => ENNReal.ofReal (cartesianGnomonicDensity z))]
  exact lintegral_congr (fun g => congrArg ENNReal.ofReal (cartesianGnomonicDensity_plane g))

end Unfoldings.Cap
