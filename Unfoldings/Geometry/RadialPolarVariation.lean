module

public import Unfoldings.Geometry.HeadingChordError
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Radial progress bounds the actual polar variation on one straight link. -/

@[expose] public section

namespace Unfoldings

/-- In an outward normalized frame, the short polar sweep is bounded by transverse displacement. -/
theorem abs_arg_one_add_le_abs_im (u : ℂ) (outward : 0 ≤ u.re) :
    |(1 + u).arg| ≤ |u.im| := by
  have real : 0 < (1 + u).re := by simpa only [Complex.add_re, Complex.one_re] using
    (show 0 < 1 + u.re by linarith)
  have range := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl real))
  have argument : (1 + u).arg = Real.arctan ((1 + u).im / (1 + u).re) := by
    rw [← Complex.tan_arg, Real.arctan_tan range.1 range.2]
  rw [argument]
  calc
    _ ≤ |(1 + u).im / (1 + u).re| := Real.abs_arctan_le_abs
    _ = |u.im| / (1 + u.re) := by
      rw [abs_div, abs_of_pos real]
      simp only [Complex.add_im, Complex.one_im, zero_add, Complex.add_re, Complex.one_re]
    _ ≤ |u.im| := (div_le_iff₀ (by linarith : 0 < 1 + u.re)).mpr (by
      nlinarith [abs_nonneg u.im])

theorem abs_im_le_sqrt_of_radial_progress (u : ℂ) {γ : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1) (progress : γ * ‖u‖ ≤ u.re) :
    |u.im| ≤ Real.sqrt (1 - γ ^ 2) * ‖u‖ := by
  have radicand : 0 ≤ 1 - γ ^ 2 := by nlinarith
  have square := mul_self_le_mul_self (mul_nonneg nonnegative (norm_nonneg u)) progress
  have norm_square := Complex.normSq_eq_norm_sq u
  rw [Complex.normSq_apply] at norm_square
  have squares : |u.im| ^ 2 ≤ (Real.sqrt (1 - γ ^ 2) * ‖u‖) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt radicand]
    nlinarith only [square, norm_square]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp squares

/-- The factor is exactly `sqrt (1 - γ²)`, with no per-crease or per-mesh loss. -/
theorem abs_arg_one_add_le_radial (u : ℂ) {γ : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1) (progress : γ * ‖u‖ ≤ u.re) :
    |(1 + u).arg| ≤ Real.sqrt (1 - γ ^ 2) * ‖u‖ :=
  (abs_arg_one_add_le_abs_im u ((mul_nonneg nonnegative (norm_nonneg _)).trans progress)).trans
    (abs_im_le_sqrt_of_radial_progress u nonnegative small progress)

/-- Real scalar products commute with multiplication after accounting for its squared scale. -/
theorem real_inner_complex_mul (a u : ℂ) : inner ℝ a (a * u) = ‖a‖ ^ 2 * u.re := by
  change (a * u * starRingEnd ℂ a).re = _
  have rearrange : a * u * starRingEnd ℂ a = u * (a * starRingEnd ℂ a) := by ring
  rw [rearrange, Complex.mul_conj', ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The polar sweep has the precise angular factor needed in the finite weighted estimate. -/
theorem radial_polar_step_bound (a v : ℂ) (nonzero : a ≠ 0) {γ : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (progress : γ * (‖a‖ * ‖v‖) ≤ inner ℝ a v) :
    ‖a‖ * |((a + v) / a).arg| ≤ Real.sqrt (1 - γ ^ 2) * ‖v‖ := by
  have positive : 0 < ‖a‖ := norm_pos_iff.mpr nonzero
  have cancel : a * (v / a) = v := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ nonzero
  have scalar := real_inner_complex_mul a (v / a)
  rw [cancel] at scalar
  rw [scalar] at progress
  have normalized : γ * ‖v / a‖ ≤ (v / a).re := by
    rw [norm_div]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos positive)).mp
    calc
      ‖a‖ ^ 2 * (γ * (‖v‖ / ‖a‖)) = γ * (‖a‖ * ‖v‖) := by field_simp
      _ ≤ ‖a‖ ^ 2 * (v / a).re := progress
  have argument : (a + v) / a = 1 + v / a := by rw [add_div, div_self nonzero]
  rw [argument]
  calc
    _ ≤ ‖a‖ * (Real.sqrt (1 - γ ^ 2) * ‖v / a‖) :=
      mul_le_mul_of_nonneg_left
        (abs_arg_one_add_le_radial _ nonnegative small normalized) positive.le
    _ = _ := by rw [norm_div]; field_simp

/-- The first link has zero polar sweep when it starts at the source. -/
theorem radial_polar_step_bound' (a v : ℂ) {γ : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (progress : γ * (‖a‖ * ‖v‖) ≤ inner ℝ a v) :
    ‖a‖ * |((a + v) / a).arg| ≤ Real.sqrt (1 - γ ^ 2) * ‖v‖ := by
  by_cases zero : a = 0
  · rw [zero, norm_zero, zero_mul]
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  · exact radial_polar_step_bound a v zero nonnegative small progress

end Unfoldings
