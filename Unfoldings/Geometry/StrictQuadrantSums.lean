module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite sum of zero or strictly up-left vectors vanishes when either coordinate does. -/

@[expose] public section

namespace Unfoldings

theorem sum_re_zero_iff_of_strict_quadrant {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (strict : ∀ i, v i = 0 ∨ (v i).re < 0 ∧ 0 < (v i).im) :
    (∑ i, v i).re = 0 ↔ ∑ i, v i = 0 := by
  constructor
  · intro zero
    have nonpositive (i : ι) : (v i).re ≤ 0 := by
      rcases strict i with equal | bounds
      · rw [equal]
        exact le_rfl
      · exact bounds.1.le
    rw [Complex.re_sum] at zero
    have each := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => nonpositive i)).mp zero
    apply Finset.sum_eq_zero
    intro i member
    rcases strict i with equal | bounds
    · exact equal
    · exact (bounds.1.ne (each i member)).elim
  · intro equal
    rw [equal, Complex.zero_re]

theorem sum_im_zero_iff_of_strict_quadrant {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (strict : ∀ i, v i = 0 ∨ (v i).re < 0 ∧ 0 < (v i).im) :
    (∑ i, v i).im = 0 ↔ ∑ i, v i = 0 := by
  constructor
  · intro zero
    have nonnegative (i : ι) : 0 ≤ (v i).im := by
      rcases strict i with equal | bounds
      · rw [equal]
        exact le_rfl
      · exact bounds.2.le
    rw [Complex.im_sum] at zero
    have each := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => nonnegative i)).mp zero
    apply Finset.sum_eq_zero
    intro i member
    rcases strict i with equal | bounds
    · exact equal
    · exact (bounds.2.ne (each i member).symm).elim
  · intro equal
    rw [equal, Complex.zero_im]

end Unfoldings
