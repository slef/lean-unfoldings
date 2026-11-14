module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Quantitative radial margins and length constants survive controlled chord errors. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem perturbed_chord_norm_upper {r q : E} {δ : ℝ}
    (error : ‖q - r‖ ≤ δ * ‖r‖) : ‖q‖ ≤ (1 + δ) * ‖r‖ := by
  have upper := norm_add_le r (q - r)
  have identity : r + (q - r) = q := by abel
  rw [identity] at upper
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem perturbed_chord_norm_lower {r q : E} {δ : ℝ}
    (error : ‖q - r‖ ≤ δ * ‖r‖) : (1 - δ) * ‖r‖ ≤ ‖q‖ := by
  have upper := norm_add_le q (r - q)
  have identity : q + (r - q) = r := by abel
  rw [identity, norm_sub_rev r q] at upper
  nlinarith

/-- The margin loss depends on relative chord error, independently of the number of links. -/
theorem radial_margin_of_chord_error {r q v : E} {d δ : ℝ}
    (nonnegative : 0 ≤ δ) (small : δ < d) (error : ‖q - r‖ ≤ δ * ‖r‖)
    (margin : d * (‖r‖ * ‖v‖) ≤ inner ℝ r v) :
    ((d - δ) / (1 + δ)) * (‖q‖ * ‖v‖) ≤ inner ℝ q v := by
  have denominator : 0 < 1 + δ := by linarith
  have coefficient : 0 ≤ (d - δ) / (1 + δ) :=
    (div_pos (sub_pos.mpr small) denominator).le
  have norm_upper := perturbed_chord_norm_upper error
  have cauchy := (abs_le.mp (abs_real_inner_le_norm (q - r) v)).1
  rw [inner_sub_left] at cauchy
  have error_scaled := mul_le_mul_of_nonneg_right error (norm_nonneg v)
  calc
    _ ≤ ((d - δ) / (1 + δ)) * (((1 + δ) * ‖r‖) * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right norm_upper (norm_nonneg v)) coefficient
    _ = (d - δ) * (‖r‖ * ‖v‖) := by
      field_simp
    _ ≤ inner ℝ q v := by nlinarith

omit [InnerProductSpace ℝ E] in
theorem length_constant_of_chord_error {r q : E} {length D δ : ℝ}
    (nonnegative : 0 ≤ D) (small : δ < 1) (error : ‖q - r‖ ≤ δ * ‖r‖)
    (length_bound : length ≤ D * ‖r‖) : length ≤ (D / (1 - δ)) * ‖q‖ := by
  have positive : 0 < 1 - δ := sub_pos.mpr small
  have lower := perturbed_chord_norm_lower error
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ positive).mpr
  calc
    length * (1 - δ) ≤ (D * ‖r‖) * (1 - δ) :=
      mul_le_mul_of_nonneg_right length_bound positive.le
    _ = D * ((1 - δ) * ‖r‖) := by ring
    _ ≤ D * ‖q‖ := mul_le_mul_of_nonneg_left lower nonnegative

end Unfoldings
