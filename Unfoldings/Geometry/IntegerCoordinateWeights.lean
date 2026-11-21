module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic

/-! An integer coordinate of a positive constituent of a convex average
cannot lie across an integer cut if the coordinate varies by at most one. -/

@[expose] public section

namespace Unfoldings

open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem intCoordinate_ge_of_average_ge (value : I → ℤ) (weight : I → ℝ) (i : I)
    (range : ∀ j, value j ≤ value i + 1) (nonnegative : ∀ j, 0 ≤ weight j)
    (total : ∑ j, weight j = 1) (positive : 0 < weight i) {lower : ℤ}
    (bound : (lower : ℝ) ≤ ∑ j, weight j * (value j : ℝ)) :
    lower ≤ value i := by
  by_contra! outside
  have pointwise (j : I) : weight j * (value j : ℝ) ≤ weight j * (lower : ℝ) := by
    have le : value j ≤ lower := by have h := range j; omega
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast le) (nonnegative j)
  have strict : weight i * (value i : ℝ) < weight i * (lower : ℝ) :=
    mul_lt_mul_of_pos_left (by exact_mod_cast outside) positive
  have sum := Finset.sum_lt_sum (s := (Finset.univ : Finset I))
    (fun j _ => pointwise j) ⟨i, Finset.mem_univ _, strict⟩
  rw [← Finset.sum_mul, total, one_mul] at sum
  exact sum.not_ge bound

theorem intCoordinate_le_of_average_le (value : I → ℤ) (weight : I → ℝ) (i : I)
    (range : ∀ j, value i ≤ value j + 1) (nonnegative : ∀ j, 0 ≤ weight j)
    (total : ∑ j, weight j = 1) (positive : 0 < weight i) {upper : ℤ}
    (bound : (∑ j, weight j * (value j : ℝ)) ≤ (upper : ℝ)) :
    value i ≤ upper := by
  have range' (j : I) : -value j ≤ -value i + 1 := by have h := range j; omega
  have bound' : ((-upper : ℤ) : ℝ) ≤ ∑ j, weight j * ((-value j : ℤ) : ℝ) := by
    push_cast
    simp only [mul_neg, Finset.sum_neg_distrib]
    exact neg_le_neg bound
  exact neg_le_neg_iff.mp
    (intCoordinate_ge_of_average_ge (fun j => -value j) weight i range'
      nonnegative total positive bound')

end Unfoldings
