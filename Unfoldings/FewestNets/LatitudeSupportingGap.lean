module

public import Unfoldings.FewestNets.LatitudeVertexBounds

/-! Quantitative support-plane comparisons for the straightened latitude rows. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- A strip's nearby vertices stay strictly above all farther rows even
after the possible squared-spacing loss in the supporting functional. -/
theorem latitude_far_cosine_lt_near {r near far loss : ℝ} (positive : 0 < r)
    (nearby : |near| ≤ 0.516 * r) (farther : 0.94 * r ≤ |far|) (range : |far| ≤ π)
    (loss_bound : loss ≤ 0.02 * r ^ 2) : cos far < cos near - loss := by
  have near_sq := pow_le_pow_left₀ (abs_nonneg near) nearby 2
  rw [sq_abs, mul_pow] at near_sq
  have far_sq := pow_le_pow_left₀ (by positivity : 0 ≤ 0.94 * r) farther 2
  rw [sq_abs, mul_pow] at far_sq
  have upper := cos_le_one_sub_mul_cos_sq range
  have pi_sq : π ^ 2 ≤ 10 := by
    have h := pow_le_pow_left₀ pi_pos.le pi_lt_d4.le 2
    linarith only [h]
  have coeff : (0.17 : ℝ) ≤ (2 / π ^ 2) * 0.94 ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < π ^ 2)).mpr
    linarith only [pi_sq]
  have loss_far : 0.17 * r ^ 2 ≤ 2 / π ^ 2 * far ^ 2 :=
    (mul_le_mul_of_nonneg_right coeff (sq_nonneg r)).trans
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left far_sq (by positivity))
  linarith only [upper, loss_far, one_sub_sq_div_two_le_cos (x := near), near_sq,
    loss_bound, sq_pos_of_pos positive]

/-- The unnormalized ordinate gap stays large and the normal of the chord
plane turns by at most 0.016 times the row scale from the strip center. -/
theorem latitude_support_tilt_of_chart {r b H Y₀ Y₁ Z₀ Z₁ c : ℝ}
    (positive : 0 < r) (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (altitude : 0.93 * r < Y₁ - Y₀) (height_eq : H = Y₁ * Z₁ - Y₀ * Z₀)
    (y₀ : |Y₀| ≤ 0.516 * r) (y₁ : |Y₁| ≤ 0.516 * r)
    (z₀ : 0.998 ≤ Z₀ ∧ Z₀ ≤ 1) (z₁ : 0.998 ≤ Z₁ ∧ Z₁ ≤ 1)
    (drop₀ : c - 0.25125 * b ^ 2 ≤ Z₀ ∧ Z₀ ≤ c)
    (drop₁ : c - 0.25125 * b ^ 2 ≤ Z₁ ∧ Z₁ ≤ c) :
    0.927 * r < H ∧ |arctan ((Z₁ - Z₀) / H)| < 0.016 * r := by
  have error (Y Z : ℝ) (y : |Y| ≤ 0.516 * r) (z : 0.998 ≤ Z ∧ Z ≤ 1) :
      |Y * (Z - 1)| ≤ 0.001032 * r := by
    have height : |Z - 1| ≤ 0.002 := abs_le.mpr ⟨by linarith only [z.1], by linarith only [z.2]⟩
    rw [abs_mul]
    calc
      _ ≤ (0.516 * r) * 0.002 :=
        mul_le_mul y height (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have H_low : 0.927 * r < H := by
    linarith only [altitude, height_eq, (abs_le.mp (error _ _ y₀ z₀)).2,
      (abs_le.mp (error _ _ y₁ z₁)).1, positive]
  have H_pos : 0 < H := (mul_pos (by norm_num) positive).trans H_low
  have difference : |Z₁ - Z₀| ≤ 0.25125 * b ^ 2 :=
    abs_le.mpr ⟨by linarith only [drop₀.2, drop₁.1], by linarith only [drop₀.1, drop₁.2]⟩
  have ratio : |(Z₁ - Z₀) / H| < 0.016 * r := by
    rw [abs_div, abs_of_pos H_pos]
    apply (div_lt_iff₀ H_pos).mpr
    have square := pow_lt_pow_left₀ b_small b_pos.le (by decide : (2 : ℕ) ≠ 0)
    have lower := mul_lt_mul_of_pos_left H_low (show 0 < 0.016 * r by positivity)
    nlinarith only [square, lower, difference, sq_pos_of_pos positive]
  exact ⟨H_low, abs_arctan_le_abs.trans_lt ratio⟩

end Unfoldings.FewestNets
