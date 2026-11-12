module

public import Unfoldings.Geometry.ComplexRotationFrame
public import Unfoldings.Cone.Sector

/-! A named nonzero ray determines an oriented frame's exact rotation phase. -/

@[expose] public section

namespace Unfoldings

theorem oriented_frame_eq_polarRay_mul (F : ℂ ≃ₗᵢ[ℝ] ℂ)
    (commutes : ∀ z w : ℂ, F (z * w) = z * F w)
    {u : ℂ} (nonzero : u ≠ 0) {α δ : ℝ}
    (original : u = (‖u‖ : ℂ) * polarRay α)
    (mapped : F u = (‖u‖ : ℂ) * polarRay δ) (z : ℂ) :
    F z = polarRay (δ - α) * z := by
  have unit : polarRay α * F 1 = polarRay δ := by
    conv_lhs at mapped => rw [original, ← Complex.real_smul, map_smul, Complex.real_smul]
    rw [show F (polarRay α) = polarRay α * F 1 from
        by simpa only [mul_one] using commutes (polarRay α) 1] at mapped
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero)) mapped
  have phase : F 1 = polarRay (δ - α) := by
    calc
      F 1 = polarRay (-α) * (polarRay α * F 1) := by
        rw [← mul_assoc, ← polarRay_add, neg_add_cancel, polarRay_zero, one_mul]
      _ = polarRay (-α) * polarRay δ := by rw [unit]
      _ = polarRay (δ - α) := by rw [← polarRay_add]; congr 1; ring
  calc
    F z = z * F 1 := by simpa only [mul_one] using commutes z 1
    _ = _ := by rw [phase, mul_comm]

/-- Two open quadrants separated by between a quarter and a half turn
cannot contain the same vector. This uses the real rotation, without an
argument branch or a nonzero-vector exception. -/
theorem not_both_quadrants_of_rotation {x y : ℂ} {κ : ℝ}
    (large : Real.pi / 2 ≤ κ) (small : κ < Real.pi)
    (rotation : x = polarRay κ * y)
    (first : 0 < x.re) (last : 0 ≤ y.re ∧ 0 < y.im) : False := by
  have sine := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) small
  have cosine := Real.cos_nonpos_of_pi_div_two_le_of_le large
    (by linarith [Real.pi_pos])
  have real := congrArg Complex.re rotation
  simp only [Complex.mul_re, polarRay_re, polarRay_im] at real
  have nonpositive := mul_nonpos_of_nonpos_of_nonneg cosine last.1
  have positive := mul_pos sine last.2
  linarith

end Unfoldings
