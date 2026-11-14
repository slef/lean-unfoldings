module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Finite Fubini estimates control weighted heading errors without a global heading cone. -/

@[expose] public section

namespace Unfoldings

variable {n : ℕ}

def futureVariation (variation : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (i < ·), variation j

def earlierLength (length : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· < j), length i

/-- The link at which variation occurs is excluded from its own earlier-length factor. -/
theorem weighted_variation_fubini (length variation : Fin n → ℝ) :
    (∑ i, length i * futureVariation variation i) =
      ∑ j, earlierLength length j * variation j := by
  simp only [futureVariation, earlierLength, Finset.sum_filter, Finset.mul_sum,
    Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  exact Finset.sum_comm

theorem weighted_futureVariation_le (length variation radius : Fin n → ℝ) {C K : ℝ}
    (constant : 0 ≤ C) (nonnegative : ∀ i, 0 ≤ variation i)
    (progress : ∀ j, earlierLength length j ≤ C * radius j)
    (angular : ∀ j, radius j * variation j ≤ K * length j) :
    (∑ i, length i * futureVariation variation i) ≤ C * K * ∑ i, length i := by
  rw [weighted_variation_fubini]
  calc
    _ ≤ ∑ j, (C * radius j) * variation j := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (progress j) (nonnegative j))
    _ ≤ ∑ j, C * (K * length j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (angular j) constant
    _ = _ := by simp only [← Finset.mul_sum, mul_assoc]

/-- Long total polar variation is allowed; its weighted cost depends only on radial progress. -/
theorem weighted_heading_budget (length variation radius error : Fin n → ℝ) {B C K δ : ℝ}
    (constant : 0 ≤ C) (budget : 0 ≤ B) (width : 0 < δ)
    (length_nonnegative : ∀ i, 0 ≤ length i) (nonnegative : ∀ i, 0 ≤ variation i)
    (progress : ∀ j, earlierLength length j ≤ C * radius j)
    (angular : ∀ j, radius j * variation j ≤ K * length j)
    (heading : ∀ i, error i ≤ B * (1 + futureVariation variation i / δ)) :
    (∑ i, length i * error i) ≤ B * (1 + C * K / δ) * ∑ i, length i := by
  have fubini := weighted_futureVariation_le length variation radius
    constant nonnegative progress angular
  calc
    _ ≤ ∑ i, length i * (B * (1 + futureVariation variation i / δ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (heading i) (length_nonnegative i))
    _ = B * ((∑ i, length i) + (∑ i, length i * futureVariation variation i) / δ) := by
      calc
        _ = ∑ i, (B * length i + (B / δ) * (length i * futureVariation variation i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    _ ≤ B * ((∑ i, length i) + (C * K * ∑ i, length i) / δ) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (div_le_div_of_nonneg_right fubini width.le)) budget
    _ = _ := by ring

end Unfoldings
