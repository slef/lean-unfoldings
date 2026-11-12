module

public import Unfoldings.Geometry.CircleInnerCornerOrder

/-! Early and late coordinate comparisons give circle order across a terminal height. -/

@[expose] public section

namespace Unfoldings

/-- The four height cases use only actual endpoint coordinates and an interior
terminal copy. No auxiliary comparison-curve avoidance property is assumed. -/
theorem circle_order_across_terminal_height {left right middle : ℂ} {a b terminal : ℝ}
    (left_re : 0 ≤ left.re) (left_im : 0 ≤ left.im)
    (right_re : 0 ≤ right.re) (right_im : 0 ≤ right.im)
    (same_radius : ‖left‖ = ‖right‖) (inside : ‖middle‖ < ‖left‖)
    (left_early : a ≤ terminal → left.re ≤ middle.re)
    (right_early : b ≤ terminal → right.im ≤ middle.im)
    (left_late : terminal ≤ a → middle.im ≤ left.im)
    (right_late : terminal ≤ b → middle.re ≤ right.re)
    (both_late : terminal ≤ a → terminal ≤ b → left.re ≤ right.re) :
    left.re ≤ right.re ∧ right.im ≤ left.im := by
  have square := congrArg (fun r : ℝ => r ^ 2) same_radius
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at square
  simp only [Complex.normSq_apply, ← pow_two] at square
  apply quadrant_circle_order left_re left_im right_re right_im square
  rcases le_total terminal a with late_left | early_left
  · rcases le_total terminal b with late_right | early_right
    · exact Or.inl (both_late late_left late_right)
    · exact Or.inr ((right_early early_right).trans (left_late late_left))
  · rcases le_total terminal b with late_right | early_right
    · exact Or.inl ((left_early early_left).trans (right_late late_right))
    · exact Or.inl (circle_order_of_inner_corner right_re right_im same_radius inside
        (left_early early_left) (right_early early_right)).le

end Unfoldings
