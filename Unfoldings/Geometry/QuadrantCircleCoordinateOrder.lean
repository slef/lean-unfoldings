module

public import Unfoldings.Geometry.WeakCircleCaps

/-! Horizontal circle order reverses vertical order in the closed positive quadrant. -/

@[expose] public section

namespace Unfoldings

theorem complex_im_le_of_norm_eq_of_re_le {z w : ℂ}
    (first_re : 0 ≤ z.re) (_last_re : 0 ≤ w.re)
    (first_im : 0 ≤ z.im) (_last_im : 0 ≤ w.im)
    (size : ‖z‖ = ‖w‖) (ordered : z.re ≤ w.re) : w.im ≤ z.im := by
  have squares := congrArg (fun r : ℝ => r ^ 2) size
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at squares
  have horizontal := mul_self_le_mul_self first_re ordered
  nlinarith

end Unfoldings
