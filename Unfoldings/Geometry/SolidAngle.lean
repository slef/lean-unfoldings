module

public import Unfoldings.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Solid angle as the angular measure induced by spatial volume

This is Mathlib's `volume.toSphere`, transported into ambient coordinates.
For a measurable unit-sphere region, its solid angle is three times the
volume of its open radial cone in the unit ball. This measure-based definition
supplies additivity before any spherical polygon area formula is proved.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped Pointwise ENNReal NNReal

/-- The usual solid-angle measure on the unit sphere, viewed in ambient space. -/
def solidAngleMeasure : Measure Space :=
  (volume : Measure Space).toSphere.map (Subtype.val : Metric.sphere (0 : Space) 1 → Space)

/-- Measurable spherical regions have the expected conical-volume interpretation. -/
theorem solidAngleMeasure_apply {s : Set Space} (measurable : MeasurableSet s)
    (unit : s ⊆ Metric.sphere (0 : Space) 1) :
    solidAngleMeasure s = 3 * volume (Set.Ioo (0 : ℝ) 1 • s) := by
  have image : (Subtype.val : Metric.sphere (0 : Space) 1 → Space) ''
      (Subtype.val ⁻¹' s) = s := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, present, rfl⟩
      exact present
    · intro z present
      exact ⟨⟨z, unit present⟩, present, rfl⟩
  rw [solidAngleMeasure, Measure.map_apply measurable_subtype_coe measurable,
    (volume : Measure Space).toSphere_apply' (measurable_subtype_coe measurable), image]
  norm_num [Space]

/-- The full unit sphere has solid angle `4π`. -/
theorem solidAngleMeasure_univ : solidAngleMeasure Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [solidAngleMeasure, Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.toSphere_apply_univ,
    EuclideanSpace.volume_ball_fin_three]
  norm_num only [Space, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.ofReal_one, one_pow, one_mul]
  have numeral : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [numeral, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

instance : IsFiniteMeasure solidAngleMeasure := by
  unfold solidAngleMeasure
  infer_instance

/-- The ambient presentation gives no mass to points away from the unit sphere. -/
theorem solidAngleMeasure_off_sphere :
    solidAngleMeasure (Metric.sphere (0 : Space) 1)ᶜ = 0 := by
  rw [solidAngleMeasure, Measure.map_apply measurable_subtype_coe
    (Metric.isClosed_sphere.measurableSet.compl)]
  have empty : (Subtype.val : Metric.sphere (0 : Space) 1 → Space) ⁻¹'
      (Metric.sphere (0 : Space) 1)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z outside
    exact outside z.property
  rw [empty, measure_empty]

/-- Intersecting an ambient set with the sphere preserves its solid angle. -/
theorem solidAngleMeasure_inter_sphere (s : Set Space) :
    solidAngleMeasure (s ∩ Metric.sphere (0 : Space) 1) = solidAngleMeasure s :=
  measure_inter_conull solidAngleMeasure_off_sphere

end Unfoldings
