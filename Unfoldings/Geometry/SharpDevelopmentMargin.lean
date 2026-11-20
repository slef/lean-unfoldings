module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Rational interval bounds for the shallow-development radial margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

private def sqrtUpper (i : Fin 20) : ℝ :=
  ![100, 100, 100, 99, 98, 97, 96, 94, 92, 90,
    87, 84, 80, 76, 72, 67, 60, 53, 44, 32] i / 100

private def intervalSlope (s : ℝ) : ℝ :=
  (1.006 + 34.204 * (1 + (100 / 157) * s)) / 100

private def intervalTailCost (k u : ℝ) : ℝ :=
  (66 / 700) * (2.012 / (1 - k * u))

private theorem shallowDevelopment_verifiedRows (i : Fin 20) :
    let l : ℝ := (i.val : ℝ) / 20
    let u : ℝ := ((i.val : ℝ) + 1) / 20
    let s := sqrtUpper i
    let k := intervalSlope s
    let a := intervalTailCost k u
    0 ≤ s ∧ 1 - l ^ 2 ≤ s ^ 2 ∧ 0 ≤ k ∧ k < 1 ∧ k * u < 1 ∧
      (3 / 100 : ℝ) < ((1 - k) / (1 + k * u) - a) / (1 + a * u) := by
  fin_cases i <;>
    norm_num [sqrtUpper, intervalSlope, intervalTailCost, Matrix.cons_val_zero,
      Matrix.cons_val_succ]

private theorem exists_shallowDevelopment_interval {γ : ℝ} (γ_pos : 0 < γ) (γ_small : γ < 1) :
    ∃ i : Fin 20, (i.val : ℝ) / 20 ≤ γ ∧ γ ≤ ((i.val : ℝ) + 1) / 20 := by
  have scaled_nonneg : 0 ≤ 20 * γ := by positivity
  have scaled_small : 20 * γ < (20 : ℝ) := by linarith
  let i : Fin 20 := ⟨⌊20 * γ⌋₊, (Nat.floor_lt scaled_nonneg).2 (by exact_mod_cast scaled_small)⟩
  refine ⟨i, ?_, ?_⟩
  · exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 20)).2
      (by simpa only [i, mul_comm] using Nat.floor_le scaled_nonneg)
  · exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 20)).2
      (by simpa only [i, mul_comm] using (Nat.lt_floor_add_one (20 * γ)).le)

/-- The elementary bounds from the shallow-development estimate imply the two
numerical radial conditions in the paper, with the square-root term retained. -/
theorem sharp_development_radial_margin {γ E S Ω : ℝ}
    (γ_pos : 0 < γ) (γ_small : γ < 1) (E_nonneg : 0 ≤ E)
    (E_bound : E ≤ ((1.006 + 34.204 * (1 + (100 / 157) * √(1 - γ ^ 2))) / 100) * γ)
    (speed_nonneg : 0 ≤ S) (speed : S ≤ 2.012) (Ω_nonneg : 0 ≤ Ω) (curvature : Ω ≤ π * γ / 100) :
    E < γ ∧
      2 * Ω / π < ((γ - E) / (1 + E) - 3 * Ω * (S / (1 - E))) /
        (1 + 3 * Ω * (S / (1 - E))) := by
  change E ≤ intervalSlope (√(1 - γ ^ 2)) * γ at E_bound
  obtain ⟨i, lower, upper⟩ := exists_shallowDevelopment_interval γ_pos γ_small
  let u : ℝ := ((i.val : ℝ) + 1) / 20
  let k := intervalSlope (sqrtUpper i)
  let a := intervalTailCost k u
  obtain ⟨s_nonneg, sq_bound, k_nonneg, k_small, ku_small, row⟩ :=
    shallowDevelopment_verifiedRows i
  have u_nonneg : 0 ≤ u := by positivity
  have γ_le : γ ≤ u := upper
  have root_bound : √(1 - γ ^ 2) ≤ sqrtUpper i := by
    apply (Real.sqrt_le_left s_nonneg).2
    have left_nonneg : 0 ≤ (i.val : ℝ) / 20 := by positivity
    have squared := pow_le_pow_left₀ left_nonneg lower 2
    linarith
  have slope_bound : intervalSlope (√(1 - γ ^ 2)) ≤ k := by
    unfold k intervalSlope
    linarith only [root_bound]
  have E_le : E ≤ k * γ := E_bound.trans (mul_le_mul_of_nonneg_right slope_bound γ_pos.le)
  have E_lt : E < γ := E_le.trans_lt (by
    simpa only [one_mul] using mul_lt_mul_of_pos_right k_small γ_pos)
  have E_lt_one : E < 1 := E_lt.trans γ_small
  have E_le_u : E ≤ k * u := E_le.trans (mul_le_mul_of_nonneg_left γ_le k_nonneg)
  have denominator_pos : 0 < 1 - k * u := sub_pos.mpr ku_small
  have cost_nonneg : 0 ≤ a := by dsimp [a, intervalTailCost]; positivity
  have cost_bound : 3 * Ω * (S / (1 - E)) ≤ a * γ := by
    have D_le : S / (1 - E) ≤ 2.012 / (1 - k * u) :=
      (div_le_div_of_nonneg_right speed (sub_nonneg.mpr E_lt_one.le)).trans
        (div_le_div_of_nonneg_left (by norm_num) denominator_pos
          (sub_le_sub_left E_le_u 1))
    have curvature' : 3 * Ω ≤ (66 / 700) * γ := calc
      _ ≤ 3 * (π * γ / 100) := mul_le_mul_of_nonneg_left curvature (by norm_num)
      _ ≤ _ := by
        have pi_bound : π ≤ 22 / 7 := by linarith [Real.pi_lt_d4]
        have bound := mul_le_mul_of_nonneg_right pi_bound γ_pos.le
        linarith only [bound]
    calc
      _ ≤ 3 * Ω * (2.012 / (1 - k * u)) :=
        mul_le_mul_of_nonneg_left D_le (by positivity)
      _ ≤ ((66 / 700) * γ) * (2.012 / (1 - k * u)) :=
        mul_le_mul_of_nonneg_right curvature' (by positivity)
      _ = a * γ := by unfold a intervalTailCost; ring
  have ordinary :
      ((1 - k) / (1 + k * u)) * γ ≤ (γ - E) / (1 + E) := calc
    _ = ((1 - k) * γ) / (1 + k * u) := by ring
    _ ≤ ((1 - k) * γ) / (1 + E) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [E_le_u])
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [E_le]) (by positivity)
  have small_curvature : 2 * Ω / π ≤ γ / 50 := (div_le_iff₀ Real.pi_pos).2 (by
    linarith only [curvature])
  let x := 3 * Ω * (S / (1 - E))
  let b := (1 - k) / (1 + k * u) - a
  have denom_low : 0 < 1 + a * u := by positivity
  have b_pos : 0 < b := by
    have h := (lt_div_iff₀ denom_low).mp row
    exact (mul_pos (by norm_num : (0 : ℝ) < 3 / 100) denom_low).trans h
  have numerator : b * γ ≤ (γ - E) / (1 + E) - x := by
    dsimp [b, x]
    linarith only [ordinary, cost_bound]
  have scale : γ / 50 < b / (1 + a * u) * γ := by
    have cmp := mul_lt_mul_of_pos_right row γ_pos
    calc
      γ / 50 < (3 / 100 : ℝ) * γ := by linarith only [γ_pos]
      _ < _ := cmp
  have x_nonneg : 0 ≤ x :=
    mul_nonneg (by positivity) (div_nonneg speed_nonneg (sub_nonneg.mpr E_lt_one.le))
  have denom_actual : 0 < 1 + x := by positivity
  have denom_order : 1 + x ≤ 1 + a * u :=
    add_le_add_right (cost_bound.trans (mul_le_mul_of_nonneg_left γ_le cost_nonneg)) 1
  refine ⟨E_lt, small_curvature.trans_lt (scale.trans_le ?_)⟩
  calc
    _ = (b * γ) / (1 + a * u) := by ring
    _ ≤ (b * γ) / (1 + x) :=
      div_le_div_of_nonneg_left (mul_nonneg b_pos.le γ_pos.le) denom_actual denom_order
    _ ≤ _ := div_le_div_of_nonneg_right numerator denom_actual.le

end Unfoldings
