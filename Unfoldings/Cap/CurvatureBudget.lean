module

public import Unfoldings.Cap.AngularCurvature
public import Unfoldings.Cap.SolidNormalArea
public import Unfoldings.Complex.Curvature

/-! Nonnegative intrinsic curvature and its mesh-independent small-tilt budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

include K in
/-- Convexity bounds the intrinsic angle directly through actual crossing counts. -/
theorem totalAngle_le_two_pi (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) : C.totalAngle Set.univ v ≤ 2 * Real.pi := by
  classical
  obtain ⟨m, c, closes, covers⟩ := C.exists_cyclic_link Set.univ v internal
  let f : Space →L[ℝ] ℝ := EuclideanSpace.proj 2
  have fne : f ≠ 0 := by
    intro equal
    have evaluated := congrArg (fun g : Space →L[ℝ] ℝ => g (Cap.northLift 0)) equal
    change (1 : ℝ) = 0 at evaluated
    norm_num at evaluated
  have pointwise (n : Space) (upper : 0 < f n) :
      angularCrossings (fun i => K.folding.germDirection (c.point i).val)
        (finRotate (m + 1)) n ≤ 2 := by
    rw [angularCrossings_eq_card]
    exact_mod_cast K.card_link_crossings_le_two c closes covers n upper
  have bound := setLIntegral_mono (μ := solidAngleMeasure) measurable_const pointwise
  change (∫⁻ n in {n | 0 < f n}, angularCrossings
    (fun i => K.folding.germDirection (c.point i).val) (finRotate (m + 1)) n ∂solidAngleMeasure) ≤
      ∫⁻ n in {n | 0 < f n}, (2 : ℝ≥0∞) ∂solidAngleMeasure at bound
  rw [K.folding.lintegral_link_crossings c closes covers f fne,
    lintegral_const, Measure.restrict_apply_univ, solidAngleMeasure_positive f fne] at bound
  have numeric : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (4 * Real.pi) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [numeric] at bound
  have real := (ENNReal.ofReal_le_ofReal_iff
    (by positivity : 0 ≤ 4 * Real.pi)).mp bound
  linarith

include K in
theorem interiorCurvature_nonneg (v : C.Vertex Set.univ) :
    0 ≤ C.interiorAngularDefect Set.univ v := by
  classical
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary, le_refl]
  · simpa only [TriangleComplex.interiorAngularDefect, ite_eq_right boundary] using
      sub_nonneg.mpr (K.totalAngle_le_two_pi v boundary)

include K in
theorem totalCurvature_nonneg : 0 ≤ C.totalInteriorAngularDefect Set.univ :=
  Finset.sum_nonneg (fun v _ => K.interiorCurvature_nonneg v)

/-- Actual curvature is bounded by the checked packing of all actual normal cones. -/
theorem ofReal_totalCurvature_le_solid_normal_area :
    ENNReal.ofReal (C.totalInteriorAngularDefect Set.univ) ≤
      ∑ v : C.Vertex Set.univ, solidAngleMeasure (K.sphericalNormalPolygon v) := by
  classical
  rw [TriangleComplex.totalInteriorAngularDefect,
    ENNReal.ofReal_sum_of_nonneg (fun v _ => K.interiorCurvature_nonneg v)]
  apply Finset.sum_le_sum
  intro v _
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_left boundary,
      ENNReal.ofReal_zero, zero_le]
  · simp only [TriangleComplex.interiorAngularDefect, ite_eq_right boundary,
      K.angular_defect_eq_solid_normal v boundary, le_refl]

/-- The positive threshold is chosen before the cap and is independent of its mesh size. -/
theorem exists_tilt_totalCurvature_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ K : ConvexCap C, K.TiltBound φ →
      C.totalInteriorAngularDefect Set.univ < ε := by
  obtain ⟨φ, bounds, budget⟩ := exists_tilt_solid_normal_area_lt (C := C) positive
  refine ⟨φ, bounds, fun K tilt => ?_⟩
  have bound := K.ofReal_totalCurvature_le_solid_normal_area.trans_lt (budget K tilt)
  exact (ENNReal.ofReal_lt_ofReal_iff positive).mp bound

end Unfoldings.ConvexCap
