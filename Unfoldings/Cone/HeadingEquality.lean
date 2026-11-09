module

public import Unfoldings.Cone.PolarEquality

/-!
# Equality of bounded real headings

On any real interval shorter than a full turn, positive-radius polar
coordinates determine the heading. Two pointed heading intervals that meet
have a union shorter than a full turn, so the same conclusion holds across
those intervals. This supports local lifts even in overlapping developments.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings

theorem polar_eq_heading_of_mem_Icc (r : ℝ≥0) (nonzero : r ≠ 0)
    (a b : ℝ) (width : b - a < 2 * Real.pi) (θ φ : ℝ)
    (left : θ ∈ Set.Icc a b) (right : φ ∈ Set.Icc a b)
    (equal : (r : ℂ) * polarRay θ = (r : ℂ) * polarRay φ) : θ = φ := by
  have real_nonzero : (r : ℝ) ≠ 0 := fun h => nonzero (NNReal.coe_injective h)
  have complex_nonzero : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr real_nonzero
  have rays := mul_left_cancel₀ complex_nonzero equal
  have exponentials : Circle.exp θ = Circle.exp φ := Subtype.ext rays
  apply Circle.exp_injOn_Ico (a := a) (b := a + 2 * Real.pi) (by linarith)
    ⟨left.1, by linarith [left.2]⟩ ⟨right.1, by linarith [right.2]⟩ exponentials

theorem polar_eq_heading_of_overlapping_intervals (r : ℝ≥0) (nonzero : r ≠ 0)
    (a b c d : ℝ) (first_width : b - a < Real.pi) (last_width : d - c < Real.pi)
    (meet_first : a ≤ d) (meet_last : c ≤ b) (θ φ : ℝ)
    (left : θ ∈ Set.Icc a b) (right : φ ∈ Set.Icc c d)
    (equal : (r : ℂ) * polarRay θ = (r : ℂ) * polarRay φ) : θ = φ := by
  have width : max b d - min a c < 2 * Real.pi := by
    rcases le_total a c with first | first <;> rcases le_total b d with last | last
    · rw [min_eq_left first, max_eq_right last]
      linarith
    · rw [min_eq_left first, max_eq_left last]
      linarith [Real.pi_pos]
    · rw [min_eq_right first, max_eq_right last]
      linarith [Real.pi_pos]
    · rw [min_eq_right first, max_eq_left last]
      linarith
  apply polar_eq_heading_of_mem_Icc r nonzero (min a c) (max b d) width θ φ
    ⟨(min_le_left _ _).trans left.1, left.2.trans (le_max_left _ _)⟩
    ⟨(min_le_right _ _).trans right.1, right.2.trans (le_max_right _ _)⟩ equal

end Unfoldings
