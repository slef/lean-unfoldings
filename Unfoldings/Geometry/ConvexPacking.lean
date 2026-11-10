module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Basic

/-! Finite convex packing bounds allow boundary contacts and lower-dimensional pieces. -/

@[expose] public section

namespace Unfoldings

open MeasureTheory MeasureTheory.Measure

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

/-- Disjoint interiors suffice for the total Haar measure bound of a finite convex packing. -/
theorem sum_measure_convex_le (μ : Measure E) [IsAddHaarMeasure μ]
    (pieces : I → Set E) (convex : ∀ i, Convex ℝ (pieces i))
    (separated : Pairwise (fun i j => Disjoint (interior (pieces i)) (interior (pieces j))))
    (region : Set E) (inside : ∀ i, pieces i ⊆ region) :
    (∑ i, μ (pieces i)) ≤ μ region := by
  have union_measure : μ (⋃ i, interior (pieces i)) = ∑ i, μ (interior (pieces i)) := by
    rw [measure_iUnion separated (fun _ => isOpen_interior.measurableSet), tsum_fintype]
  calc
    (∑ i, μ (pieces i)) = ∑ i, μ (interior (pieces i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measure_interior_of_null_frontier ((convex i).addHaar_frontier μ)).symm
    _ = μ (⋃ i, interior (pieces i)) := union_measure.symm
    _ ≤ μ region := measure_mono (Set.iUnion_subset (fun i => interior_subset.trans (inside i)))

end Unfoldings
