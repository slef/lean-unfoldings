module

public import Mathlib.Geometry.Euclidean.Volume.Measure

/-! Nonexpansive maps do not increase normalized Euclidean Hausdorff measure. -/

@[expose] public section

open MeasureTheory

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The normalization factor is the same in both ambient dimensions. -/
theorem LipschitzWith.euclideanHausdorffMeasure_image_le_of_one {f : X → Y}
    (nonexpansive : LipschitzWith 1 f) (d : ℕ) (s : Set X) :
    μHE[d] (f '' s) ≤ μHE[d] s := by
  have estimate : μH[(d : ℝ)] (f '' s) ≤ μH[(d : ℝ)] s := by
    simpa using nonexpansive.hausdorffMeasure_image_le (Nat.cast_nonneg d) s
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact smul_le_smul_left _ estimate
