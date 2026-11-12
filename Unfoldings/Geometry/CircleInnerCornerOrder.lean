module

public import Unfoldings.Geometry.BankRadialOrder

/-! An interior corner orders two first-quadrant circle points. -/

@[expose] public section

namespace Unfoldings

/-- A point strictly inside the circle cannot lie northeast of a reversed pair
of circle endpoints. This handles two crossings before a terminal pinch. -/
theorem circle_order_of_inner_corner {left right middle : ℂ}
    (right_re : 0 ≤ right.re) (right_im : 0 ≤ right.im)
    (same_radius : ‖left‖ = ‖right‖) (inside : ‖middle‖ < ‖left‖)
    (horizontal : left.re ≤ middle.re) (vertical : right.im ≤ middle.im) :
    left.re < right.re := by
  by_contra reversed
  have re_bound := mul_self_le_mul_self right_re ((not_lt.mp reversed).trans horizontal)
  have im_bound := mul_self_le_mul_self right_im vertical
  have middle_square := Complex.normSq_eq_norm_sq middle
  have right_square := Complex.normSq_eq_norm_sq right
  simp only [Complex.normSq_apply, ← pow_two] at middle_square right_square
  rw [same_radius] at inside
  nlinarith [norm_nonneg middle, norm_nonneg right]

end Unfoldings
