module

public import Unfoldings.Geometry.SolidAngleHemisphere
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Angular length as an average of hemisphere crossings

A finite family of genuine spatial edges has total angular length equal to
half the integral of its scalar-product sign changes over any hemisphere.
The identity does not assume convexity or simplicity of the family. Convexity
is needed separately to show that a vertex link has zero or two crossings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal NNReal

variable {I : Type*} [Fintype I]

/-- Number of strict scalar-product sign changes, in a measure-friendly scalar type. -/
def angularCrossings (ray : I → Space) (next : I → I) (n : Space) : ℝ≥0∞ :=
  ∑ i, (spatialSignChange (ray i) (ray (next i))).indicator (fun _ => 1) n

theorem angularCrossings_measurable (ray : I → Space) (next : I → I) :
    Measurable (angularCrossings ray next) :=
  Finset.measurable_sum Finset.univ (fun i _ =>
    measurable_const.indicator (spatialSignChange_measurable (ray i) (ray (next i))))

/-- A direct discrete spherical Crofton identity, derived from actual spatial lune measures. -/
theorem lintegral_angularCrossings (ray : I → Space) (next : I → I)
    (genuine : ∀ i, ray i ≠ 0) (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    (∫⁻ n in {n | 0 < f n}, angularCrossings ray next n ∂solidAngleMeasure) =
      ENNReal.ofReal (2 * ∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) := by
  simp only [angularCrossings]
  rw [lintegral_finsetSum Finset.univ
    (fun i _ => measurable_const.indicator (spatialSignChange_measurable _ _))]
  have piece (i : I) :
      (∫⁻ n in {n | 0 < f n}, (spatialSignChange (ray i) (ray (next i))).indicator
        (fun _ => (1 : ℝ≥0∞)) n ∂solidAngleMeasure) =
      ENNReal.ofReal (2 * InnerProductGeometry.angle (ray i) (ray (next i))) := by
    rw [setLIntegral_indicator (spatialSignChange_measurable _ _), lintegral_const,
      Measure.restrict_apply_univ, one_mul]
    exact solidAngleMeasure_spatialSignChange_inter_positive _ _
      (genuine i) (genuine (next i)) f nonzero
  simp only [piece]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (InnerProductGeometry.angle_nonneg (ray i) (ray (next i)))), Finset.mul_sum]

/-- The measure-theoretic part of the vertex Gauss identity.

The crossing assertion must still be proved from actual convex geometry;
it is not part of any cap input structure. -/
theorem angular_defect_eq_solidAngle_of_crossings (ray : I → Space) (next : I → I)
    (genuine : ∀ i, ray i ≠ 0) (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0)
    (normal : Set Space) (measurable : MeasurableSet normal)
    (upper : normal ⊆ {n | 0 < f n})
    (crossings : ∀ᵐ n ∂solidAngleMeasure.restrict {n | 0 < f n},
      angularCrossings ray next n = ({n | 0 < f n} \ normal).indicator (fun _ => 2) n) :
    ENNReal.ofReal (2 * Real.pi - ∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) =
      solidAngleMeasure normal := by
  let H : Set Space := {n | 0 < f n}
  have measurable_H : MeasurableSet H := (isOpen_lt continuous_const f.continuous).measurableSet
  have integral := lintegral_angularCrossings ray next genuine f nonzero
  have counted : (∫⁻ n in H, angularCrossings ray next n ∂solidAngleMeasure) =
      2 * solidAngleMeasure (H \ normal) := by
    rw [lintegral_congr_ae crossings, setLIntegral_indicator (measurable_H.diff measurable),
      Set.inter_eq_left.mpr Set.sdiff_subset, lintegral_const, Measure.restrict_apply_univ]
  have angle_nonnegative : 0 ≤ ∑ i, InnerProductGeometry.angle (ray i) (ray (next i)) :=
    Finset.sum_nonneg (fun i _ => InnerProductGeometry.angle_nonneg _ _)
  have double : ENNReal.ofReal (2 * ∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) =
      2 * ENNReal.ofReal (∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) := by
    simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using
      ENNReal.ofReal_mul (p := 2)
        (q := ∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) (by norm_num)
  have equal : ENNReal.ofReal (∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) =
      solidAngleMeasure (H \ normal) := by
    apply (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
    exact double.symm.trans (integral.symm.trans counted)
  have balance : solidAngleMeasure normal +
      ENNReal.ofReal (∑ i, InnerProductGeometry.angle (ray i) (ray (next i))) =
        ENNReal.ofReal (2 * Real.pi) := by
    rw [equal]
    calc
      _ = solidAngleMeasure (H \ normal) + solidAngleMeasure (H ∩ normal) := by
        rw [Set.inter_eq_right.mpr upper, add_comm]
      _ = solidAngleMeasure H := measure_sdiff_add_inter H measurable
      _ = ENNReal.ofReal (2 * Real.pi) := solidAngleMeasure_positive f nonzero
  have real := congrArg ENNReal.toReal balance
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal angle_nonnegative,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] at real
  calc
    _ = ENNReal.ofReal (solidAngleMeasure normal).toReal := by congr 1; linarith
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

end Unfoldings
