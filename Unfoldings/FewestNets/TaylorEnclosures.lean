module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-! Explicit real Taylor remainders for the finite certificate checker. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real Set
open scoped Nat

/-- Evaluate a Taylor polynomial at zero from its integer derivative data. -/
def integerTaylor (coefficient : ℕ → ℤ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((coefficient k : ℝ) / (k ! : ℝ)) * x ^ k

/-- Taylor error with a unit bound on every derivative. -/
theorem abs_sub_integerTaylor_le {f : ℝ → ℝ} (smooth : ContDiff ℝ ⊤ f)
    {coefficient : ℕ → ℤ} (at_zero : ∀ k, iteratedDeriv k f 0 = coefficient k)
    (bounded : ∀ k y, |iteratedDeriv k f y| ≤ 1)
    (n : ℕ) (x : ℝ) :
    |f x - integerTaylor coefficient n x| ≤ |x| ^ (n + 1) / ((n + 1)! : ℝ) := by
  by_cases zero : x = 0
  · have c0 : f 0 = (coefficient 0 : ℝ) := by simpa using at_zero 0
    simp [zero, integerTaylor, Finset.sum_range_succ', ← c0]
  have nn : 0 ≠ x := Ne.symm zero
  obtain ⟨z, _, remainder⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := n) nn (smooth.of_le le_top).contDiffOn
  have poly : taylorWithinEval f n (uIcc 0 x) 0 x = integerTaylor coefficient n x := by
    rw [taylor_within_apply, integerTaylor]
    apply Finset.sum_congr rfl
    intro k _
    have local_smooth : ContDiffAt ℝ k f (0 : ℝ) := (smooth.of_le le_top).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc nn) local_smooth left_mem_uIcc,
      at_zero, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [poly, sub_zero] at remainder
  rw [remainder, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg ((n + 1)! ) : 0 ≤ ((n + 1)! : ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (bounded (n + 1) z)
    (pow_nonneg (abs_nonneg x) _)

def sinCoefficient (k : ℕ) : ℤ := if k % 2 = 0 then 0 else (-1) ^ (k / 2)

def cosCoefficient (k : ℕ) : ℤ := if k % 2 = 0 then (-1) ^ (k / 2) else 0

theorem iteratedDeriv_sin_zero (k : ℕ) : iteratedDeriv k sin 0 = sinCoefficient k := by
  by_cases even : k % 2 = 0
  · have eq : k = 2 * (k / 2) := by omega
    nth_rw 1 [eq]
    rw [iteratedDeriv_even_sin]
    simp [sinCoefficient, even, Pi.mul_apply, Pi.pow_apply]
  · have eq : k = 2 * (k / 2) + 1 := by omega
    nth_rw 1 [eq]
    rw [iteratedDeriv_odd_sin]
    simp [sinCoefficient, even, Pi.mul_apply, Pi.pow_apply]

theorem iteratedDeriv_cos_zero (k : ℕ) : iteratedDeriv k cos 0 = cosCoefficient k := by
  by_cases even : k % 2 = 0
  · have eq : k = 2 * (k / 2) := by omega
    nth_rw 1 [eq]
    rw [iteratedDeriv_even_cos]
    simp [cosCoefficient, even, Pi.mul_apply, Pi.pow_apply]
  · have eq : k = 2 * (k / 2) + 1 := by omega
    nth_rw 1 [eq]
    rw [iteratedDeriv_odd_cos]
    simp [cosCoefficient, even, Pi.mul_apply, Pi.pow_apply]

theorem abs_sin_sub_integerTaylor_le (n : ℕ) (x : ℝ) :
    |sin x - integerTaylor sinCoefficient n x| ≤ |x| ^ (n + 1) / ((n + 1)! : ℝ) :=
  abs_sub_integerTaylor_le contDiff_sin iteratedDeriv_sin_zero abs_iteratedDeriv_sin_le_one n x

theorem abs_cos_sub_integerTaylor_le (n : ℕ) (x : ℝ) :
    |cos x - integerTaylor cosCoefficient n x| ≤ |x| ^ (n + 1) / ((n + 1)! : ℝ) :=
  abs_sub_integerTaylor_le contDiff_cos iteratedDeriv_cos_zero abs_iteratedDeriv_cos_le_one n x

end Unfoldings.FewestNets
