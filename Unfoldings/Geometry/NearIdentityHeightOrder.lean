module

public import Unfoldings.Geometry.NearIdentityMargins

/-! A near-identity linear map preserves right/down order at equal sweep height. -/

@[expose] public section

namespace Unfoldings

theorem linear_near_identity_same_height_order (A : ℂ →ₗ[ℝ] ℂ) {ε : ℝ}
    (nonnegative : 0 ≤ ε) (small : ε ≤ 1 / 2)
    (error : ∀ z, ‖A z - z‖ ≤ ε * ‖z‖)
    {p q : ℂ} (horizontal : p.re ≤ q.re)
    (height : p.re + p.im = q.re + q.im) :
    0 ≤ (A (q - p)).re ∧ (A (q - p)).im ≤ 0 := by
  have vertical : q.im - p.im ≤ 0 := by linarith
  have size : ‖q - p‖ ≤ 2 * (q.re - p.re) := by
    have bound := Complex.norm_le_abs_re_add_abs_im (q - p)
    simp only [Complex.sub_re, Complex.sub_im,
      abs_of_nonneg (sub_nonneg.mpr horizontal), abs_of_nonpos vertical] at bound
    linarith
  have estimate : ‖A (q - p) - (q - p)‖ ≤ 2 * ε * (q.re - p.re) :=
    (error _).trans (by nlinarith [mul_le_mul_of_nonneg_left size nonnegative])
  have real := (abs_le.mp ((Complex.abs_re_le_norm _).trans estimate)).1
  have imaginary := (abs_le.mp ((Complex.abs_im_le_norm _).trans estimate)).2
  simp only [Complex.sub_re] at real
  simp only [Complex.sub_im] at imaginary
  have positive_progress := mul_nonneg (by linarith : 0 ≤ 1 - 2 * ε)
    (sub_nonneg.mpr horizontal)
  constructor <;> nlinarith

end Unfoldings
