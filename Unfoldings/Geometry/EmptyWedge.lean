module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith

/-!
# An empty forward wedge at a finite-set extremum

Maximizing a linear functional over the internal vertices leaves its entire
forward open halfplane empty. Any sufficiently narrow cone within that
halfplane can serve as the gap between near-quadrants. This avoids needing a
nearest-boundary selection merely to obtain an empty angular gap.
-/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_empty_forward_halfspace (vertices : Finset E) (nonempty : vertices.Nonempty)
    (height : E →ₗ[ℝ] ℝ) :
    ∃ q ∈ vertices, ∀ p ∈ vertices, height (p - q) ≤ 0 := by
  obtain ⟨q, present, maximal⟩ := vertices.exists_max_image height nonempty
  refine ⟨q, present, fun p member => ?_⟩
  rw [map_sub, sub_nonpos]
  exact maximal p member

/-- A positive direction wedge contains no other marked point when apexed at a height maximizer. -/
theorem exists_empty_positive_wedge (vertices : Finset E) (nonempty : vertices.Nonempty)
    (height : E →ₗ[ℝ] ℝ) (u v : E) (upward : 0 < height u) (forward : 0 < height v) :
    ∃ q ∈ vertices, ∀ p ∈ vertices, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      p - q = a • u + b • v → a = 0 ∧ b = 0 ∧ p = q := by
  obtain ⟨q, present, empty⟩ := exists_empty_forward_halfspace vertices nonempty height
  refine ⟨q, present, fun p member a b ha hb expression => ?_⟩
  have bound := empty p member
  rw [expression, map_add, map_smul, map_smul] at bound
  change a * height u + b * height v ≤ 0 at bound
  have left : a = 0 := by
    by_contra nonzero
    have positive : 0 < a := lt_of_le_of_ne ha (Ne.symm nonzero)
    have product := mul_pos positive upward
    linarith [mul_nonneg hb forward.le]
  have right : b = 0 := by
    rw [left, zero_mul, zero_add] at bound
    by_contra nonzero
    have positive : 0 < b := lt_of_le_of_ne hb (Ne.symm nonzero)
    exact (not_lt_of_ge bound) (mul_pos positive forward)
  refine ⟨left, right, ?_⟩
  rw [left, right, zero_smul, zero_smul, zero_add] at expression
  exact sub_eq_zero.mp expression

end Unfoldings
