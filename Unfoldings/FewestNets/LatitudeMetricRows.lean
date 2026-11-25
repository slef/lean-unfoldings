module

public import Unfoldings.FewestNets.LatitudeRows

/-! Metric longitude spacing, and the numerical scale of the two polar selectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

def latitudeLongitudeStep (a : ℝ) (j : ℕ) : ℝ := 2 * π / latitudeRowSize a j

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
theorem latitude_sin_half_radius :
    0.999 * (latitudeRadius a / 2) < sin (latitudeRadius a / 2) := by
  let h := latitudeRadius a / 2
  have h_pos : 0 < h := div_pos (latitudeRadius_pos positive) (by norm_num)
  have h_small : h < 0.058 := by
    change latitudeRadius a / 2 < 0.058
    linarith only [latitudeRadius_lt small]
  have remainder := Real.abs_sub_sin_le h
  rw [abs_of_pos h_pos] at remainder
  have square := pow_le_pow_left₀ h_pos.le h_small.le 2
  have cube := mul_le_mul_of_nonneg_left square h_pos.le
  change 0.999 * h < sin h
  nlinarith only [(abs_le.mp remainder).2, cube, h_pos]

include positive small in
theorem latitude_sin_lower {x : ℝ} (lower : latitudeRadius a / 2 ≤ x)
    (upper : x ≤ π - latitudeRadius a / 2) :
    0.999 * (latitudeRadius a / 2) < sin x := by
  have first := latitude_sin_half_radius positive small
  have left : -(π / 2) ≤ latitudeRadius a / 2 := by
    linarith only [pi_pos, latitudeRadius_pos positive]
  apply first.trans_le
  by_cases hx : x ≤ π / 2
  · exact sin_le_sin_of_le_of_le_pi_div_two left hx lower
  · rw [← sin_pi_sub x]
    exact sin_le_sin_of_le_of_le_pi_div_two left (by linarith only [hx]) (by linarith only [upper])

include positive small in
theorem latitude_row_size_pos {j : ℕ} (row : j ≤ latitudeStripCount a) :
    0 < latitudeRowSize a j := by
  obtain ⟨low, up⟩ := latitudeColatitude_bounds positive small row
  have lower := latitude_sin_lower positive small low up
  have r_pos := latitudeRadius_pos positive
  have s_pos : 0 < sin (latitudeColatitude a j) := by linarith only [r_pos, lower]
  have b_pos : 0 < latitudeSpacing a := mul_pos (mul_pos (by norm_num) positive) r_pos
  exact Nat.one_le_ceil_iff.mpr (div_pos (mul_pos (by positivity) s_pos) b_pos)

include positive small in
/-- The paper's longitude-spacing interval, with the ceiling included. -/
theorem latitudeLongitudeStep_bounds {j : ℕ} (row : j ≤ latitudeStripCount a) :
    let s := sin (latitudeColatitude a j)
    latitudeSpacing a / (1.076 * s) < latitudeLongitudeStep a j ∧
      latitudeLongitudeStep a j ≤ latitudeSpacing a / s := by
  let s := sin (latitudeColatitude a j)
  let b := latitudeSpacing a
  let k := latitudeRowSize a j
  let r := latitudeRadius a
  obtain ⟨low, up⟩ := latitudeColatitude_bounds positive small row
  have lower : 0.999 * (r / 2) < s := latitude_sin_lower positive small low up
  have r_pos : 0 < r := latitudeRadius_pos positive
  have s_pos : 0 < s := by linarith only [r_pos, lower]
  have b_pos : 0 < b := mul_pos (mul_pos (by norm_num) positive) r_pos
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (latitude_row_size_pos positive small row)
  have ceil_low : 2 * π * s / b ≤ (k : ℝ) := Nat.le_ceil _
  have ceil_high : (k : ℝ) < 2 * π * s / b + 1 := Nat.ceil_lt_add_one (by positivity)
  have b_small : b < 0.236 * r := latitudeSpacing_lt positive small
  have b_circle : b < 0.076 * (2 * π * s) := by
    have a := mul_lt_mul_of_pos_left lower (show 0 < (0.076 * 2 * 3.14 : ℝ) by norm_num)
    have c := mul_lt_mul_of_pos_right pi_gt_d2 s_pos
    linarith only [b_small, r_pos, a, c]
  have extra : 1 < 0.076 * (2 * π * s) / b :=
    (lt_div_iff₀ b_pos).mpr (by simpa only [one_mul] using b_circle)
  have upper : (k : ℝ) * b < 1.076 * s * (2 * π) := by
    have bound : (k : ℝ) < 1.076 * (2 * π * s / b) := by
      have eq : 0.076 * (2 * π * s) / b = 0.076 * (2 * π * s / b) := by
        field_simp <;> ring
      rw [eq] at extra
      linarith only [ceil_high, extra]
    have scaled := mul_lt_mul_of_pos_right bound b_pos
    have cancel : 1.076 * (2 * π * s / b) * b = 1.076 * s * (2 * π) := by
      field_simp <;> ring
    rwa [cancel] at scaled
  change b / (1.076 * s) < (2 * π) / k ∧ (2 * π) / k ≤ b / s
  constructor
  · exact (div_lt_div_iff₀ (mul_pos (by norm_num) s_pos) k_pos).mpr (by
      simpa only [mul_comm] using upper)
  · exact (div_le_div_iff₀ k_pos s_pos).mpr (by
      simpa only [mul_comm] using (div_le_iff₀ b_pos).mp ceil_low)

include positive small in
/-- The first and last latitude rings have the same polar polygon size. -/
theorem latitude_first_last_row_size_eq :
    latitudeRowSize a 0 = latitudeRowSize a (latitudeStripCount a) := by
  unfold latitudeRowSize
  rw [latitudeColatitude_last positive small, sin_pi_sub]
  congr 3
  simp [latitudeColatitude]

include positive small in
/-- The polar row has the side count and angular spacing required by the round selector estimate. -/
theorem latitude_polar_size_bounds :
    let k := latitudeRowSize a 0
    0.999 * π / (0.45 * a) < (k : ℝ) ∧ (k : ℝ) < 8 / a ∧
      π / (k : ℝ) < 0.451 * a ∧ 0.451 * a < √a / 2 := by
  let k := latitudeRowSize a 0
  let r := latitudeRadius a
  let b := latitudeSpacing a
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (latitude_row_size_pos positive small (Nat.zero_le _))
  have r_pos : 0 < r := latitudeRadius_pos positive
  have b_pos : 0 < b := mul_pos (mul_pos (by norm_num) positive) r_pos
  have b_eq : b = 0.45 * a * r := rfl
  have s : latitudeColatitude a 0 = r / 2 := by simp [latitudeColatitude, r]
  have lower : 0.999 * (r / 2) < sin (r / 2) := latitude_sin_half_radius positive small
  have upper := sin_le (by positivity : 0 ≤ r / 2)
  have k_eq : k = ⌈2 * π * sin (r / 2) / b⌉₊ := by
    unfold k latitudeRowSize
    rw [s]
  have ceil_low : 2 * π * sin (r / 2) / b ≤ (k : ℝ) := by
    rw [k_eq]
    exact Nat.le_ceil _
  have ceil_high : (k : ℝ) < 2 * π * sin (r / 2) / b + 1 := by
    rw [k_eq]
    exact Nat.ceil_lt_add_one
      (div_nonneg (mul_nonneg (by positivity) (by linarith only [lower, r_pos])) b_pos.le)
  have small_lo : 0.999 * π / (0.45 * a) < (k : ℝ) := by
    apply lt_of_lt_of_le _ ceil_low
    rw [b_eq]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have bound := mul_lt_mul_of_pos_left lower (by positivity : 0 < 0.9 * π * a)
    nlinarith only [bound]
  have small_hi : (k : ℝ) < 8 / a := by
    apply ceil_high.trans_le
    calc
      _ ≤ 2 * π * (r / 2) / b + 1 :=
        add_le_add_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left upper (by positivity : 0 ≤ 2 * π)) b_pos.le) 1
      _ = π / (0.45 * a) + 1 := by rw [b_eq]; field_simp
      _ ≤ _ := by
        apply (le_div_iff₀ positive).mpr
        have cap : (π / (0.45 * a) + 1) * a = π / 0.45 + a := by
          field_simp <;> ring
        rw [cap]
        have first := div_le_div_of_nonneg_right pi_lt_d4.le (by norm_num : 0 ≤ (0.45 : ℝ))
        have second := small.trans (div_le_div_of_nonneg_right pi_lt_d4.le (by norm_num))
        linarith only [first, second]
  refine ⟨small_lo, small_hi, (div_lt_iff₀ k_pos).mpr ?_, ?_⟩
  · have root := (div_lt_iff₀ (show 0 < (0.45 * a) by positivity)).mp small_lo
    have lower := mul_lt_mul_of_pos_right root (show (0 : ℝ) < 0.451 by norm_num)
    linarith only [lower, pi_pos]
  · have sq := sq_sqrt positive.le
    have root : √a < 1 := by
      by_contra! large
      have bound := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) large 2
      linarith only [bound, sq, small, pi_lt_d4]
    have scaled := mul_lt_mul_of_pos_right root (Real.sqrt_pos.2 positive)
    nlinarith only [scaled, sq, positive]

end Unfoldings.FewestNets
