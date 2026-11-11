module

public import Unfoldings.Geometry.QuadrantRotationOrder

/-! Strict coordinate opening of a positive rotation between actual quadrant bank vectors. -/

@[expose] public section

namespace Unfoldings

/-- A positive sub-half-turn rotation in the open quadrant strictly moves left and up. -/
theorem quadrant_rotation_coordinate_strict {x y : ℂ} {κ : ℝ}
    (positive : 0 < κ) (small : κ < Real.pi) (rotation : y = polarRay κ * x)
    (xre : 0 < x.re) (xim : 0 < x.im) (yre : 0 < y.re) (yim : 0 < y.im) :
    y.re < x.re ∧ x.im < y.im := by
  have sine := Real.sin_pos_of_pos_of_lt_pi positive small
  have cosine := Real.cos_le_one κ
  have real := congrArg Complex.re rotation
  simp only [Complex.mul_re, polarRay_re, polarRay_im] at real
  have horizontal : y.re < x.re := by
    have first := mul_le_mul_of_nonneg_right cosine xre.le
    have last := mul_pos sine xim
    linarith
  have norms : ‖y‖ = ‖x‖ := by rw [rotation, norm_mul, norm_polarRay, one_mul]
  have squares : y.re ^ 2 + y.im ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    have identity (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [identity, identity, norms]
  have first := mul_self_lt_mul_self yre.le horizontal
  refine ⟨horizontal, ?_⟩
  by_contra below
  have vertical : y.im ≤ x.im := le_of_not_gt below
  have last := mul_self_le_mul_self yim.le vertical
  nlinarith

end Unfoldings
