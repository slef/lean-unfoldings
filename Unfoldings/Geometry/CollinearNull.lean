module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Collinear planar convex hulls have zero actual Lebesgue area. -/

@[expose] public section

namespace Unfoldings

open MeasureTheory

theorem volume_convexHull_eq_zero_of_collinear {S : Set Plane} (collinear : Collinear ℝ S) :
    volume (convexHull ℝ S) = 0 := by
  have proper : affineSpan ℝ S ≠ ⊤ := by
    intro equal
    have rank := collinear.finrank_le_one
    have span : vectorSpan ℝ S = ⊤ := by
      rw [← direction_affineSpan, equal, AffineSubspace.direction_top]
    rw [span] at rank
    norm_num [Plane] at rank
  exact measure_mono_null (convexHull_subset_affineSpan S)
    (Measure.addHaar_affineSubspace volume (affineSpan ℝ S) proper)

end Unfoldings
