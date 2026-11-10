module

public import Unfoldings.Geometry.EuclideanArea

/-! Quantitative Lipschitz estimates for normalized Euclidean Hausdorff measure. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The normalization factor depends on the measured dimension, not the ambient dimension. -/
theorem LipschitzOnWith.euclideanHausdorffMeasure_image_le {K : ℝ≥0} {f : X → Y} {s : Set X}
    (bound : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  have estimate := bound.hausdorffMeasure_image_le (Nat.cast_nonneg d)
  simp only [ENNReal.rpow_natCast] at estimate
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  calc
    _ ≤ _ • ((K : ℝ≥0∞) ^ d * μH[(d : ℝ)] s) := smul_le_smul_left _ estimate
    _ = _ := by simp only [ENNReal.smul_def, smul_eq_mul]; ring

