module

public import Unfoldings.Geometry.AffineConeBounds

/-! Quantitative linear proximity to the identity supplies the four strict strip axis tests. -/

@[expose] public section

namespace Unfoldings

theorem affineAxisMargins_pos_of_linear_error (A : ℂ →ᵃ[ℝ] ℂ) {c : ℝ}
    (small : c < 1 / 2) (error : ∀ z, ‖A.linear z - z‖ ≤ c * ‖z‖) :
    ∀ j, 0 < affineAxisMargins A j := by
  have first : ‖A.linear 1 - 1‖ ≤ c := by simpa only [norm_one, mul_one] using error 1
  have last : ‖A.linear Complex.I - Complex.I‖ ≤ c := by
    simpa only [Complex.norm_I, mul_one] using error Complex.I
  have first_re := abs_le.mp ((Complex.abs_re_le_norm _).trans first)
  have first_im := abs_le.mp ((Complex.abs_im_le_norm _).trans first)
  have last_re := abs_le.mp ((Complex.abs_re_le_norm _).trans last)
  have last_im := abs_le.mp ((Complex.abs_im_le_norm _).trans last)
  simp only [Complex.sub_re, Complex.one_re] at first_re
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at first_im
  simp only [Complex.sub_re, Complex.I_re, sub_zero] at last_re
  simp only [Complex.sub_im, Complex.I_im] at last_im
  intro j
  fin_cases j
  · change 0 < (A.linear 1).re + (A.linear 1).im
    linarith
  · change 0 < (A.linear 1).re - (A.linear 1).im
    linarith
  · change 0 < (A.linear Complex.I).re + (A.linear Complex.I).im
    linarith
  · change 0 < (A.linear Complex.I).im - (A.linear Complex.I).re
    linarith

end Unfoldings
