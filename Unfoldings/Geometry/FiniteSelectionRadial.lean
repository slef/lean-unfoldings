module

public import Unfoldings.Geometry.FiniteSelectionError
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Positive linear tests give radial progress through arbitrary continuous chart switches. -/

@[expose] public section

namespace Unfoldings

theorem finite_affine_selection_linear_bound_along_path {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    (L : ℂ →ₗ[ℝ] ℝ) (c : ℝ)
    (axis_bounds : ∀ i, c ≤ L ((A i).linear 1) ∧ c ≤ L ((A i).linear Complex.I))
    {F : ℂ → ℂ} {p q : ℂ} (P : Path p q)
    (Fcontinuous : Continuous (fun t => F (P t)))
    (selection : ∀ t, ∃ i, F (P t) = A i (P t))
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => (P t).im)) :
    c * ((q.re + q.im) - (p.re + p.im)) ≤ L (F q) - L (F p) := by
  have bound (i : ι) (a b : ℂ) (re : a.re ≤ b.re) (im : a.im ≤ b.im) :
      c * ((b.re + b.im) - (a.re + a.im)) ≤ L (A i b) - L (A i a) := by
    have split : b - a = (b.re - a.re) • (1 : ℂ) + (b.im - a.im) • Complex.I := by
      apply Complex.ext <;> simp
    have linear : (A i).linear (b - a) = A i b - A i a := (A i).linear_apply_vsub b a
    have equation : L (A i b) - L (A i a) =
        (b.re - a.re) * L ((A i).linear 1) + (b.im - a.im) * L ((A i).linear Complex.I) := by
      rw [← map_sub, ← linear, split, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
      rfl
    have first := mul_le_mul_of_nonneg_left (axis_bounds i).1 (sub_nonneg.mpr re)
    have last := mul_le_mul_of_nonneg_left (axis_bounds i).2 (sub_nonneg.mpr im)
    linarith
  let input := fun t => (P t).re + (P t).im
  have input_continuous : Continuous input :=
    (Complex.continuous_re.comp P.continuous).add (Complex.continuous_im.comp P.continuous)
  have Lcontinuous := L.continuous_of_finiteDimensional
  have total := finite_selection_coordinate_bound input (fun t => L (F (P t)))
    input_continuous (Lcontinuous.comp Fcontinuous) c (fun i t => L (A i (P t)))
    (fun i => Lcontinuous.comp ((continuous i).comp P.continuous))
    (fun i a b ordered => by
      have estimate := bound i (P a) (P b) (horizontal ordered) (vertical ordered)
      dsimp only [input]
      linarith)
    (fun t => (selection t).imp (fun _ same => congrArg L same))
  simpa only [input, Path.source, Path.target] using total

theorem finite_affine_selection_norm_lt_along_path {ι : Type*} [Finite ι]
    (A : ι → ℂ →ᵃ[ℝ] ℂ) (continuous : ∀ i, Continuous (A i))
    {F : ℂ → ℂ} {p q : ℂ} (source : ℂ) {c : ℝ} (positive : 0 < c)
    (axis_bounds : ∀ i, c ≤ inner ℝ (F p - source) ((A i).linear 1) ∧
      c ≤ inner ℝ (F p - source) ((A i).linear Complex.I))
    (P : Path p q) (Fcontinuous : Continuous (fun t => F (P t)))
    (selection : ∀ t, ∃ i, F (P t) = A i (P t))
    (horizontal : Monotone (fun t => (P t).re))
    (vertical : Monotone (fun t => (P t).im))
    (height : p.re + p.im < q.re + q.im) : ‖F p - source‖ < ‖F q - source‖ := by
  let w := F p - source
  let L := (innerSL ℝ w).toLinearMap
  have bound := finite_affine_selection_linear_bound_along_path A continuous L c axis_bounds P
    Fcontinuous selection horizontal vertical
  change c * ((q.re + q.im) - (p.re + p.im)) ≤ inner ℝ w (F q) - inner ℝ w (F p) at bound
  have inner_positive : 0 < inner ℝ w (F q - F p) := by
    rw [inner_sub_right]
    exact (mul_pos positive (sub_pos.mpr height)).trans_le bound
  have expression : F q - source = w + (F q - F p) := by dsimp only [w]; abel
  have square := norm_add_sq_real w (F q - F p)
  rw [← expression] at square
  change ‖w‖ < ‖F q - source‖
  nlinarith [norm_nonneg w, norm_nonneg (F q - source), sq_nonneg ‖F q - F p‖]

end Unfoldings
