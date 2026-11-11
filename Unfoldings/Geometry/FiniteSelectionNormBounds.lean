module

public import Unfoldings.Geometry.FiniteSelectionError

/-! Upper norm estimates survive arbitrary continuous switches between finitely many branches. -/

@[expose] public section

namespace Unfoldings

theorem finite_selection_norm_bound {ι : Type*} [Finite ι]
    (input : unitInterval → ℝ) (selected : unitInterval → ℂ)
    (input_continuous : Continuous input) (selected_continuous : Continuous selected) (c : ℝ)
    (branch : ι → unitInterval → ℂ) (branch_continuous : ∀ i, Continuous (branch i))
    (bound : ∀ i a b, a ≤ b → ‖branch i b - branch i a‖ ≤ c * (input b - input a))
    (selection : ∀ t, ∃ i, selected t = branch i t) :
    ‖selected 1 - selected 0‖ ≤ 2 * c * (input 1 - input 0) := by
  have real_bound := finite_selection_abs_bound input (fun t => (selected t).re)
    input_continuous (Complex.continuous_re.comp selected_continuous) c
    (fun i t => (branch i t).re) (fun i => Complex.continuous_re.comp (branch_continuous i))
    (fun i a b ordered => (Complex.abs_re_le_norm _).trans (bound i a b ordered))
    (fun t => (selection t).imp (fun _ same => congrArg Complex.re same))
  have imaginary_bound := finite_selection_abs_bound input (fun t => (selected t).im)
    input_continuous (Complex.continuous_im.comp selected_continuous) c
    (fun i t => (branch i t).im) (fun i => Complex.continuous_im.comp (branch_continuous i))
    (fun i a b ordered => (Complex.abs_im_le_norm _).trans (bound i a b ordered))
    (fun t => (selection t).imp (fun _ same => congrArg Complex.im same))
  have norm_bound := Complex.norm_le_abs_re_add_abs_im (selected 1 - selected 0)
  simp only [Complex.sub_re, Complex.sub_im] at norm_bound
  linarith

theorem finite_affine_selection_norm_bound_along_path {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i)) {c : ℝ} (nonnegative : 0 ≤ c)
    (linear_bound : ∀ i z, ‖(A i).linear z‖ ≤ c * ‖z‖)
    {F : ℂ → ℂ} {p q : ℂ} (P : Path p q) (input : unitInterval → ℝ)
    (input_continuous : Continuous input)
    (path_bound : ∀ a b, a ≤ b → ‖P b - P a‖ ≤ input b - input a)
    (Fcontinuous : Continuous (fun t => F (P t)))
    (selection : ∀ t, ∃ i, F (P t) = A i (P t)) :
    ‖F q - F p‖ ≤ 2 * c * (input 1 - input 0) := by
  have bound := finite_selection_norm_bound input (fun t => F (P t)) input_continuous Fcontinuous c
    (fun i t => A i (P t)) (fun i => (continuous i).comp P.continuous)
    (fun i a b ordered => ?_) selection
  · simpa only [Path.source, Path.target] using bound
  · have linear : (A i).linear (P b - P a) = A i (P b) - A i (P a) :=
      (A i).linear_apply_vsub _ _
    rw [← linear]
    exact (linear_bound i _).trans (mul_le_mul_of_nonneg_left (path_bound a b ordered) nonnegative)

end Unfoldings
