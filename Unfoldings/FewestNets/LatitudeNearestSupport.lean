module

public import Unfoldings.FewestNets.LatitudeClosestRow

/-! The nearest-site rule maximizes the actual circular support on a latitude row. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- A site within half a row step of the meridian maximizes the cosine
over all sites, including sites across the periodic seam. -/
theorem cos_longitude_le_of_nearest {k j₀ : ℕ} (positive : 0 < k) {θ : ℝ}
    (closest : |θ - rowLongitude k j₀| ≤ π / k) (j : ℕ) :
    cos (θ - rowLongitude k j) ≤ cos (θ - rowLongitude k j₀) := by
  let d := 2 * π / (k : ℝ)
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr positive
  have d_pos : 0 < d := by positivity
  have period : d * (k : ℝ) = 2 * π := div_mul_cancel₀ _ k_pos.ne'
  have half : d / 2 = π / (k : ℝ) := by dsimp only [d]; ring
  have at_row (i : ℕ) : rowLongitude k i = d * i := by unfold rowLongitude; dsimp only [d]; ring
  rw [at_row j₀, ← half] at closest
  rw [at_row j, at_row j₀]
  let near := θ - d * j₀
  let x := θ - d * j
  let q : ℤ := ⌊(x + π) / (2 * π)⌋
  let t := x - (q : ℝ) * (2 * π)
  let index : ℤ := (j₀ : ℤ) - (j : ℤ) - q * (k : ℤ)
  have two_pos : 0 < 2 * π := by positivity
  have floor_low := (le_div_iff₀ two_pos).mp (Int.floor_le ((x + π) / (2 * π)))
  have floor_high := (div_lt_iff₀ two_pos).mp (Int.lt_floor_add_one ((x + π) / (2 * π)))
  have t_abs : |t| ≤ π := by
    apply abs_le.mpr
    change (q : ℝ) * (2 * π) ≤ x + π at floor_low
    change x + π < ((q : ℝ) + 1) * (2 * π) at floor_high
    constructor <;> dsimp only [t] <;> linarith only [floor_low, floor_high]
  have formula : t = near + d * (index : ℝ) := by
    dsimp only [t, near, x, index]
    push_cast
    rw [← period]
    ring
  have close : |near| ≤ d / 2 := closest
  have not_closer : |near| ≤ |t| := by
    rcases lt_trichotomy index 0 with left | equal | right
    · have idx : (index : ℝ) ≤ -1 := by exact_mod_cast (show index ≤ -1 by omega)
      have scaled := mul_le_mul_of_nonneg_left idx d_pos.le
      have bound : t ≤ -(d / 2) := by
        rw [formula]
        linarith only [scaled, (abs_le.mp close).2]
      exact close.trans ((le_neg_of_le_neg bound).trans (neg_le_abs t))
    · simp only [formula, equal, Int.cast_zero, mul_zero, add_zero, le_refl]
    · have idx : (1 : ℝ) ≤ index := by exact_mod_cast (show 1 ≤ index by omega)
      have scaled := mul_le_mul_of_nonneg_left idx d_pos.le
      have bound : d / 2 ≤ t := by
        rw [formula]
        linarith only [scaled, (abs_le.mp close).1]
      exact close.trans (bound.trans (le_abs_self t))
  have monotone := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) t_abs not_closer
  rw [cos_abs, cos_abs] at monotone
  change cos (x - (q : ℝ) * (2 * π)) ≤ cos near at monotone
  rwa [cos_sub_int_mul_two_pi] at monotone

end Unfoldings.FewestNets
