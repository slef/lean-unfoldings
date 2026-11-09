module

public import Unfoldings.Cone.Sector

/-!
# Equality in closed full-turn polar coordinates

At positive radius, two headings in the closed full-turn interval represent
the same point exactly at the same heading or at its two outer endpoints.
The radius itself is always determined by the norm.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings

theorem polar_radius_eq (r s : ℝ≥0) (θ φ : ℝ)
    (equal : (r : ℂ) * polarRay θ = (s : ℂ) * polarRay φ) : r = s := by
  apply NNReal.coe_injective
  have norms := congrArg norm equal
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg r.coe_nonneg, abs_of_nonneg s.coe_nonneg, norm_polarRay, mul_one] using norms

theorem polarRay_eq_cases (θ φ : ℝ)
    (θbounds : θ ∈ Set.Icc 0 (2 * Real.pi)) (φbounds : φ ∈ Set.Icc 0 (2 * Real.pi))
    (equal : polarRay θ = polarRay φ) :
    θ = φ ∨ (θ = 0 ∧ φ = 2 * Real.pi) ∨ (θ = 2 * Real.pi ∧ φ = 0) := by
  have exponentials : Circle.exp θ = Circle.exp φ := Subtype.ext equal
  have injective := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
  have zero_bounds : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  rcases lt_or_eq_of_le θbounds.2 with θsmall | θlast
  · rcases lt_or_eq_of_le φbounds.2 with φsmall | φlast
    · exact Or.inl (injective ⟨θbounds.1, θsmall⟩ ⟨φbounds.1, φsmall⟩ exponentials)
    · have last_zero : Circle.exp φ = Circle.exp 0 := by
        rw [φlast, Circle.exp_two_pi, Circle.exp_zero]
      exact Or.inr (Or.inl
        ⟨injective ⟨θbounds.1, θsmall⟩ zero_bounds (exponentials.trans last_zero), φlast⟩)
  · rcases lt_or_eq_of_le φbounds.2 with φsmall | φlast
    · have last_zero : Circle.exp θ = Circle.exp 0 := by
        rw [θlast, Circle.exp_two_pi, Circle.exp_zero]
      exact Or.inr (Or.inr
        ⟨θlast, injective ⟨φbounds.1, φsmall⟩ zero_bounds (exponentials.symm.trans last_zero)⟩)
    · exact Or.inl (θlast.trans φlast.symm)

theorem polar_eq_heading_cases (r : ℝ≥0) (nonzero : r ≠ 0) (θ φ : ℝ)
    (θbounds : θ ∈ Set.Icc 0 (2 * Real.pi)) (φbounds : φ ∈ Set.Icc 0 (2 * Real.pi))
    (equal : (r : ℂ) * polarRay θ = (r : ℂ) * polarRay φ) :
    θ = φ ∨ (θ = 0 ∧ φ = 2 * Real.pi) ∨ (θ = 2 * Real.pi ∧ φ = 0) := by
  have real_nonzero : (r : ℝ) ≠ 0 := fun h => nonzero (NNReal.coe_injective h)
  have complex_nonzero : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr real_nonzero
  exact polarRay_eq_cases θ φ θbounds φbounds (mul_left_cancel₀ complex_nonzero equal)

end Unfoldings
