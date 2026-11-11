module

public import Unfoldings.Topology.FiniteSelectionBounds
public import Unfoldings.Geometry.MonotoneStripPaths

/-! Quantitative position errors along monotone paths survive continuous face-chart changes. -/

@[expose] public section

namespace Unfoldings

theorem finite_selection_error_along_path {ι : Type*} [Finite ι]
    (branch : ι → ℂ → ℂ) (branch_continuous : ∀ i, Continuous (branch i)) (c : ℝ)
    (branch_error : ∀ i (a b : ℂ), a.re ≤ b.re → a.im ≤ b.im →
      ‖(branch i b - b) - (branch i a - a)‖ ≤
        c * ((b.re + b.im) - (a.re + a.im)))
    {F : ℂ → ℂ} {p q : ℂ} (P : Path p q)
    (continuous : Continuous (fun t => F (P t)))
    (selection : ∀ t, ∃ i, F (P t) = branch i (P t))
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => (P t).im)) :
    ‖(F q - q) - (F p - p)‖ ≤ 2 * c * ((q.re + q.im) - (p.re + p.im)) := by
  let input := fun t => (P t).re + (P t).im
  have input_continuous : Continuous input :=
    (Complex.continuous_re.comp P.continuous).add (Complex.continuous_im.comp P.continuous)
  have error_continuous : Continuous (fun t => F (P t) - P t) := continuous.sub P.continuous
  have real_bound := finite_selection_abs_bound input
    (fun t => (F (P t) - P t).re) input_continuous
    (Complex.continuous_re.comp error_continuous) c
    (fun i t => (branch i (P t) - P t).re)
    (fun i => Complex.continuous_re.comp
      (((branch_continuous i).comp P.continuous).sub P.continuous))
    (fun i a b ordered => (Complex.abs_re_le_norm _).trans
      (branch_error i (P a) (P b) (horizontal ordered) (vertical ordered)))
    (fun t => (selection t).imp (fun _ same => congrArg (fun r => (r - P t).re) same))
  have imaginary_bound := finite_selection_abs_bound input
    (fun t => (F (P t) - P t).im) input_continuous
    (Complex.continuous_im.comp error_continuous) c
    (fun i t => (branch i (P t) - P t).im)
    (fun i => Complex.continuous_im.comp
      (((branch_continuous i).comp P.continuous).sub P.continuous))
    (fun i a b ordered => (Complex.abs_im_le_norm _).trans
      (branch_error i (P a) (P b) (horizontal ordered) (vertical ordered)))
    (fun t => (selection t).imp (fun _ same => congrArg (fun r => (r - P t).im) same))
  have norm_bound := Complex.norm_le_abs_re_add_abs_im ((F q - q) - (F p - p))
  simp only [input, Path.source, Path.target] at real_bound imaginary_bound
  simp only [Complex.sub_re, Complex.sub_im] at norm_bound real_bound imaginary_bound
  linarith

theorem affine_near_identity_cone_error (A : ℂ →ᵃ[ℝ] ℂ) {c : ℝ} (nonnegative : 0 ≤ c)
    (linear_error : ∀ z : ℂ, ‖A.linear z - z‖ ≤ c * ‖z‖)
    {a b : ℂ} (horizontal : a.re ≤ b.re) (vertical : a.im ≤ b.im) :
    ‖(A b - b) - (A a - a)‖ ≤ c * ((b.re + b.im) - (a.re + a.im)) := by
  have linear : A.linear (b - a) = A b - A a := A.linear_apply_vsub b a
  have expression : (A b - b) - (A a - a) = A.linear (b - a) - (b - a) := by
    rw [linear]
    abel
  rw [expression]
  have norm_bound := Complex.norm_le_abs_re_add_abs_im (b - a)
  simp only [Complex.sub_re, Complex.sub_im, abs_of_nonneg (sub_nonneg.mpr horizontal),
    abs_of_nonneg (sub_nonneg.mpr vertical)] at norm_bound
  calc
    _ ≤ c * ‖b - a‖ := linear_error _
    _ ≤ c * ((b.re - a.re) + (b.im - a.im)) :=
      mul_le_mul_of_nonneg_left norm_bound nonnegative
    _ = _ := by ring

end Unfoldings
