module

public import Unfoldings.Geometry.ConvexPacking
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Total real variation from disjoint intervals, independently of their enumeration order. -/

@[expose] public section

namespace Unfoldings

/-- Disjoint inclination intervals in one bounded range have bounded total angular variation. -/
theorem sum_abs_sub_le_of_disjoint_intervals {I : Type*} [Fintype I]
    (a b : I → ℝ) {lower upper : ℝ} (range_nonempty : lower ≤ upper)
    (bounds : ∀ i, a i ∈ Set.Icc lower upper ∧ b i ∈ Set.Icc lower upper)
    (separated : Pairwise (fun i j => Disjoint
      (Set.Ioo (min (a i) (b i)) (max (a i) (b i)))
      (Set.Ioo (min (a j) (b j)) (max (a j) (b j))))) :
    (∑ i, |a i - b i|) ≤ upper - lower := by
  let pieces (i : I) := Set.uIcc (a i) (b i)
  have interior_separated : Pairwise (fun i j =>
      Disjoint (interior (pieces i)) (interior (pieces j))) := by
    simpa only [pieces, Set.uIcc, interior_Icc] using separated
  have contained (i : I) : pieces i ⊆ Set.Icc lower upper := by
    intro x member
    exact ⟨(le_min (bounds i).1.1 (bounds i).2.1).trans member.1,
      member.2.trans (max_le (bounds i).1.2 (bounds i).2.2)⟩
  have packing := sum_measure_convex_le MeasureTheory.volume pieces
    (fun i => convex_uIcc (a i) (b i)) interior_separated (Set.Icc lower upper) contained
  simp only [pieces, Set.uIcc, Real.volume_Icc, max_sub_min_eq_abs, abs_sub_comm] at packing
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg (a i - b i))] at packing
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr range_nonempty)).mp packing

end Unfoldings
