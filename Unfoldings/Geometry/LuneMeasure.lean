module

public import Unfoldings.Geometry.AngularLune

/-! Exact solid angle of a spherical lune from the uniform azimuth law. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal NNReal

/-- One strict lune determined by two horizontal normal directions separated by `θ`. -/
def canonicalLune (θ : ℝ) : Set Space :=
  {z | 0 < (complexHorizontal z).re ∧
    Real.cos θ * (complexHorizontal z).re + Real.sin θ * (complexHorizontal z).im < 0}

theorem canonicalLune_measurable (θ : ℝ) : MeasurableSet (canonicalLune θ) := by
  have horizontal := complexHorizontal.continuous_of_finiteDimensional
  exact ((isOpen_lt continuous_const (Complex.continuous_re.comp horizontal)).inter
    (isOpen_lt ((Complex.continuous_re.comp horizontal).const_mul _ |>.add
      ((Complex.continuous_im.comp horizontal).const_mul _)) continuous_const)).measurableSet

/-- The solid angle of a lune of aperture `θ` is exactly `2θ`. -/
theorem solidAngleMeasure_canonicalLune {θ : ℝ} (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi) :
    solidAngleMeasure (canonicalLune θ) = ENNReal.ofReal (2 * θ) := by
  let B : Set Real.Angle :=
    Metric.ball ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle) (θ / 2)
  have nonzero : ∀ᵐ z ∂solidAngleMeasure, complexHorizontal z ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using solidAngleMeasure_complexHorizontal_zero
  have regions : canonicalLune θ =ᵐ[solidAngleMeasure] azimuth ⁻¹' B := by
    filter_upwards [nonzero] with z hz
    exact propext (mem_luneBall_iff_signs hz nonnegative small).symm
  calc
    _ = solidAngleMeasure (azimuth ⁻¹' B) := measure_congr regions
    _ = azimuthMeasure B := (Measure.map_apply azimuth_measurable measurableSet_ball).symm
    _ = (2 : ℝ≥0) • volume B := by
      rw [azimuthMeasure_eq_two_volume, Measure.smul_apply]
    _ = ENNReal.ofReal (2 * θ) := by
      have size : volume B = ENNReal.ofReal θ := by
        dsimp only [B]
        rw [Real.Angle.volume_ball _ (by linarith : θ / 2 ≤ Real.pi)]
        congr 1
        ring
      rw [size, ENNReal.smul_def, smul_eq_mul]
      have numeral : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      norm_num only [ENNReal.coe_ofNat]
      rw [numeral, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

end Unfoldings
