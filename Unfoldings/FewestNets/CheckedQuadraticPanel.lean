module

public import Unfoldings.FewestNets.CheckedReal

/-! Kernel tests for a quadratic being strictly positive on the unit interval. -/

@[expose] public section

namespace Unfoldings.FewestNets

variable {D : ℕ} (hD : 0 < D)

/-- Check the sign of a convex quadratic using its derivatives at the
endpoints or the completed-square minimum. -/
def checkPositiveQuadraticPanel {x y A : ℝ}
    (first : CheckedReal D x) (last : CheckedReal D y) (curvature : CheckedReal D A) : Bool :=
  let slope := (last.sub first).sub curvature
  let terminal := (last.sub first).add curvature
  let four : CheckedReal D (4 : ℝ) := (CheckedReal.rat D 4).convert (by norm_num)
  first.isPositive && last.isPositive &&
    (slope.isPositive || terminal.neg.isPositive ||
      ((((four.mul hD curvature).mul hD first).sub (slope.square hD)).isPositive))

/-- The tested quadratic is positive, including when its minimum is inside
the panel. The definition exposes its endpoint values rather than its constant term. -/
theorem positive_of_checkPositiveQuadraticPanel {x y A : ℝ}
    (first : CheckedReal D x) (last : CheckedReal D y) (curvature : CheckedReal D A)
    (nonnegative : 0 ≤ A) (check : checkPositiveQuadraticPanel hD first last curvature = true)
    {t : ℝ} (bounds : t ∈ Set.Icc 0 1) :
    0 < (1 - t) * x + t * y - t * (1 - t) * A := by
  simp only [checkPositiveQuadraticPanel, Bool.and_eq_true, Bool.or_eq_true] at check
  have x_pos := CheckedReal.positive_of_isPositive hD _ check.1.1
  have y_pos := CheckedReal.positive_of_isPositive hD _ check.1.2
  rcases check.2 with (increasing | decreasing) | minimum
  · have slope := CheckedReal.positive_of_isPositive hD _ increasing
    have linear := mul_nonneg bounds.1 slope.le
    have square := mul_nonneg (sq_nonneg t) nonnegative
    rw [show (1 - t) * x + t * y - t * (1 - t) * A =
      x + t * ((y - x) - A) + t ^ 2 * A by ring]
    linarith only [x_pos, linear, square]
  · have slope := CheckedReal.positive_of_isPositive hD _ decreasing
    have linear := mul_nonneg (sub_nonneg.mpr bounds.2) slope.le
    have square := mul_nonneg (sq_nonneg (1 - t)) nonnegative
    rw [show (1 - t) * x + t * y - t * (1 - t) * A =
      y + (1 - t) * -((y - x) + A) + (1 - t) ^ 2 * A by ring]
    linarith only [y_pos, linear, square]
  · have positive := CheckedReal.positive_of_isPositive hD _ minimum
    have A_pos : 0 < A := by
      by_contra! zero
      have eq := le_antisymm zero nonnegative
      rw [eq, mul_zero, zero_mul, zero_sub] at positive
      linarith only [positive, sq_nonneg (y - x - 0)]
    have square := sq_nonneg (2 * A * t + (y - x - A))
    have h : 0 < 4 * A * ((1 - t) * x + t * y - t * (1 - t) * A) := by
      rw [show 4 * A * ((1 - t) * x + t * y - t * (1 - t) * A) =
        (4 * A * x - (y - x - A) ^ 2) + (2 * A * t + (y - x - A)) ^ 2 by ring]
      linarith only [positive, square]
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * A)).mp h

end Unfoldings.FewestNets
