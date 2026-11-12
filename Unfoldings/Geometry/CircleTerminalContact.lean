module

public import Unfoldings.Geometry.CircleTerminalOrder

/-! Coincident circle endpoints must both lie beyond a strictly interior terminal. -/

@[expose] public section

namespace Unfoldings

theorem circle_contact_forces_both_late {left right middle : ℂ} {a b terminal : ℝ}
    (right_re : 0 ≤ right.re) (right_im : 0 ≤ right.im)
    (same_radius : ‖left‖ = ‖right‖) (inside : ‖middle‖ < ‖left‖)
    (left_early : a ≤ terminal → left.re ≤ middle.re)
    (right_early : b ≤ terminal → right.im ≤ middle.im)
    (left_late : terminal ≤ a → middle.im < left.im)
    (right_late : terminal ≤ b → middle.re < right.re)
    (same : left = right) : terminal ≤ a ∧ terminal ≤ b := by
  by_cases first : terminal ≤ a
  · by_cases last : terminal ≤ b
    · exact ⟨first, last⟩
    · have bound := right_early (le_of_not_ge last)
      rw [← same] at bound
      exact ((left_late first).not_ge bound).elim
  · by_cases last : terminal ≤ b
    · have bound := right_late last
      rw [← same] at bound
      exact (bound.not_ge (left_early (le_of_not_ge first))).elim
    · have strict := circle_order_of_inner_corner right_re right_im same_radius inside
        (left_early (le_of_not_ge first)) (right_early (le_of_not_ge last))
      rw [same] at strict
      exact (lt_irrefl _ strict).elim

end Unfoldings
