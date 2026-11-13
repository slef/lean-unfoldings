module

public import Unfoldings.Roof.LinkCrossingBound
public import Unfoldings.Roof.Boundary
public import Unfoldings.Cap.CurvatureBudget

/-! Nonnegative intrinsic curvature and its mesh-independent small-tilt budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory
open scoped ENNReal

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

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

include K in
/-- Interior curvature of any selected finite subregion is bounded by the full cap budget. -/
theorem sum_interiorAngularDefect_le_totalCurvature (s : Finset (C.Vertex Set.univ)) :
    (∑ v ∈ s, C.interiorAngularDefect Set.univ v) ≤ C.totalInteriorAngularDefect Set.univ := by
  unfold TriangleComplex.totalInteriorAngularDefect
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun v _ _ => K.interiorCurvature_nonneg v)

end Unfoldings.ConvexRoof
