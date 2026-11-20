module

public import Unfoldings.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A quantitative radial margin at an edge start persists throughout the entire edge. -/

@[expose] public section

namespace Unfoldings

theorem radial_margin_along_ray_of_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r d : E} {γ t : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (time : 0 ≤ t) (margin : γ * (‖r‖ * ‖d‖) ≤ inner ℝ r d) :
    γ * (‖r + t • d‖ * ‖d‖) ≤ inner ℝ (r + t • d) d := by
  have normbound : ‖r + t • d‖ ≤ ‖r‖ + t * ‖d‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg time] using norm_add_le r (t • d)
  calc
    _ ≤ γ * ((‖r‖ + t * ‖d‖) * ‖d‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right normbound (norm_nonneg _)) nonnegative
    _ = γ * (‖r‖ * ‖d‖) + γ * (t * ‖d‖ ^ 2) := by ring
    _ ≤ inner ℝ r d + t * ‖d‖ ^ 2 :=
      add_le_add margin (mul_le_of_le_one_left (mul_nonneg time (sq_nonneg _)) small)
    _ = inner ℝ (r + t • d) d := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

theorem radial_margin_along_ray {r d : Plane} {γ t : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (time : 0 ≤ t) (margin : γ * (‖r‖ * ‖d‖) ≤ inner ℝ r d) :
    γ * (‖r + t • d‖ * ‖d‖) ≤ inner ℝ (r + t • d) d :=
  radial_margin_along_ray_of_inner nonnegative small time margin

end Unfoldings
