module

public import Unfoldings.Geometry.FiniteSelectionRadial

/-! Quantitative position margins and linear chart error imply actual radial progress. -/

@[expose] public section

namespace Unfoldings

theorem affine_axis_inner_lower_bound_of_error (A : ℂ →ᵃ[ℝ] ℂ) (w : ℂ) {δ : ℝ}
    (error : ∀ z, ‖A.linear z - z‖ ≤ δ * ‖z‖) :
    w.re - δ * ‖w‖ ≤ inner ℝ w (A.linear 1) ∧
      w.im - δ * ‖w‖ ≤ inner ℝ w (A.linear Complex.I) := by
  have first_norm : ‖A.linear 1 - 1‖ ≤ δ := by
    simpa only [norm_one, mul_one] using error 1
  have last_norm : ‖A.linear Complex.I - Complex.I‖ ≤ δ := by
    simpa only [Complex.norm_I, mul_one] using error Complex.I
  have first := (abs_le.mp ((abs_real_inner_le_norm w (A.linear 1 - 1)).trans
    (mul_le_mul_of_nonneg_left first_norm (norm_nonneg w)))).1
  have last := (abs_le.mp ((abs_real_inner_le_norm w (A.linear Complex.I - Complex.I)).trans
    (mul_le_mul_of_nonneg_left last_norm (norm_nonneg w)))).1
  rw [inner_sub_right] at first last
  have horizontal : inner ℝ w (1 : ℂ) = w.re := by simp [Complex.inner]
  have vertical : inner ℝ w Complex.I = w.im := by simp [Complex.inner]
  rw [horizontal] at first
  rw [vertical] at last
  constructor <;> nlinarith

theorem finite_near_identity_selection_radial {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    {F : ℂ → ℂ} {p q : ℂ} (source : ℂ) {δ μ M r : ℝ} (nonnegative : 0 ≤ δ)
    (positive : 0 < r) (small : δ * M < μ)
    (error : ∀ i z, ‖(A i).linear z - z‖ ≤ δ * ‖z‖)
    (horizontal_margin : μ * r ≤ (F p - source).re)
    (vertical_margin : μ * r ≤ (F p - source).im)
    (norm_bound : ‖F p - source‖ ≤ M * r)
    (P : Path p q) (Fcontinuous : Continuous (fun t => F (P t)))
    (selection : ∀ t, ∃ i, F (P t) = A i (P t))
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => (P t).im))
    (height : p.re + p.im < q.re + q.im) : ‖F p - source‖ < ‖F q - source‖ := by
  let c := (μ - δ * M) * r
  have cpositive : 0 < c := mul_pos (sub_pos.mpr small) positive
  apply finite_affine_selection_norm_lt_along_path A continuous source cpositive ?_ P
    Fcontinuous selection horizontal vertical height
  intro i
  have bounds := affine_axis_inner_lower_bound_of_error (A i) (F p - source) (error i)
  have product := mul_le_mul_of_nonneg_left norm_bound nonnegative
  constructor <;> dsimp only [c] <;> nlinarith [bounds.1, bounds.2]

end Unfoldings
