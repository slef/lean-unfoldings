module

public import Unfoldings.Cone.Sector
public import Mathlib.Tactic.Linarith

/-! A nonnegative small rigid bank rotation inside one quadrant orders its actual coordinates. -/

@[expose] public section

namespace Unfoldings

/-- Positive rotation inside the closed first quadrant moves left and up; zero permits contact. -/
theorem quadrant_rotation_coordinate_order {x y : ℂ} {κ : ℝ}
    (nonnegative : 0 ≤ κ) (small : κ ≤ Real.pi) (rotation : y = polarRay κ * x)
    (xre : 0 ≤ x.re) (xim : 0 ≤ x.im) (yre : 0 ≤ y.re) (yim : 0 ≤ y.im) :
    y.re ≤ x.re ∧ x.im ≤ y.im := by
  have sine := Real.sin_nonneg_of_nonneg_of_le_pi nonnegative small
  have cosine := Real.cos_le_one κ
  have horizontal : y.re ≤ x.re := by
    have real := congrArg Complex.re rotation
    simp only [Complex.mul_re, polarRay_re, polarRay_im] at real
    have first := mul_le_mul_of_nonneg_right cosine xre
    have last := mul_nonneg sine xim
    linarith
  have norms : ‖y‖ = ‖x‖ := by rw [rotation, norm_mul, norm_polarRay, one_mul]
  have squares : y.re ^ 2 + y.im ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    have identity (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [identity, identity, norms]
  refine ⟨horizontal, ?_⟩
  by_contra below
  have vertical : y.im < x.im := lt_of_not_ge below
  have first := mul_self_le_mul_self yre horizontal
  have last := mul_self_lt_mul_self yim vertical
  nlinarith

end Unfoldings
