module

public import Unfoldings.FewestNets.LatitudeVertexBounds

/-! The paper's base, height, and long-side bounds for the actual latitude chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- Closest-row assignment bounds both weighted longitude offsets of each triangle vertex. -/
theorem latitude_weighted_longitude_bounds {a : ℝ} (positive : 0 < a)
    (small : a ≤ π / 6) {j : ℕ} (row : j ≤ latitudeStripCount a) {ell w : ℝ}
    (latitude_gap : |ell - latitudeColatitude a j| ≤ latitudeRadius a / 2)
    (offset : |w| ≤ latitudeLongitudeStep a j / 2) :
    sin ell * |w| ≤ 1.005 * latitudeSpacing a ∧
      sin (latitudeColatitude a j) * |w| ≤ latitudeSpacing a / 2 := by
  let s := sin (latitudeColatitude a j)
  let r := latitudeRadius a
  let b := latitudeSpacing a
  obtain ⟨low, high⟩ := latitudeColatitude_bounds positive small row
  have s_lower : 0.999 * (r / 2) < s := latitude_sin_lower positive small low high
  have r_pos : 0 < r := latitudeRadius_pos positive
  have s_pos : 0 < s := by linarith only [r_pos, s_lower]
  have spacing : latitudeLongitudeStep a j ≤ b / s :=
    (latitudeLongitudeStep_bounds positive small row).2
  have row_bound : s * |w| ≤ b / 2 := by
    have weighted := mul_le_mul_of_nonneg_left
      (offset.trans (div_le_div_of_nonneg_right spacing (by norm_num : (0 : ℝ) ≤ 2))) s_pos.le
    calc
      _ ≤ s * (b / s / 2) := weighted
      _ = _ := by field_simp [s_pos.ne']
  have difference : sin ell - s ≤ r / 2 :=
    (le_abs_self _).trans ((abs_sin_sub_sin_le ell (latitudeColatitude a j)).trans latitude_gap)
  have sine_ratio : sin ell ≤ 2.01 * s := by linarith only [difference, s_lower, r_pos]
  refine ⟨?_, row_bound⟩
  have first := mul_le_mul_of_nonneg_right sine_ratio (abs_nonneg w)
  have second := mul_le_mul_of_nonneg_left row_bound (by norm_num : (0 : ℝ) ≤ 2.01)
  nlinarith only [first, second]

private theorem latitude_sine_at_least {t : ℝ} (positive : 0 ≤ t) (small : t ≤ 0.058) :
    0.999 * t ≤ sin t := by
  have bound := pow_le_pow_left₀ positive small 2
  have cube := mul_le_mul_of_nonneg_right bound positive
  have sine := abs_sub_sin_le t
  rw [abs_of_nonneg positive] at sine
  nlinarith only [(abs_le.mp sine).2, cube, positive]

/-- With the two base sites equally spaced about the midpoint, their
gnomonic horizontal separation has the claimed quantitative base length. -/
theorem latitude_chart_base_bounds {r b s d Z : ℝ}
    (r_pos : 0 < r) (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (s_lower : 0.999 * (r / 2) < s) (Z_lower : 0.998 < Z) (Z_upper : Z ≤ 1)
    (spacing_lower : b / (1.076 * s) < d) (spacing_upper : d ≤ b / s) :
    0.92 * b < 2 * s * sin (d / 2) / Z ∧ 2 * s * sin (d / 2) / Z < 1.01 * b := by
  have s_pos : 0 < s := by linarith only [r_pos, s_lower]
  have Z_pos : 0 < Z := by linarith only [Z_lower]
  have d_pos : 0 < d := (div_pos b_pos (by positivity : (0 : ℝ) < 1.076 * s)).trans spacing_lower
  have base_low := (div_lt_iff₀ (by positivity : (0 : ℝ) < 1.076 * s)).mp spacing_lower
  have base_up := (le_div_iff₀ s_pos).mp spacing_upper
  have h_upper : d / 2 < 0.237 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have b_bound : b < 0.474 * s := by linarith only [s_lower, r_pos, b_small]
    have d_bound := (mul_lt_mul_iff_of_pos_right s_pos).mp (base_up.trans_lt b_bound)
    linarith only [d_bound]
  have sine_lower : 0.990 * (d / 2) ≤ sin (d / 2) := by
    have rem := abs_sub_sin_le (d / 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ d / 2)] at rem
    have square := pow_le_pow_left₀ (by positivity : 0 ≤ d / 2) h_upper.le 2
    have cube := mul_le_mul_of_nonneg_right square (by positivity : 0 ≤ d / 2)
    nlinarith only [(abs_le.mp rem).2, cube, d_pos]
  constructor
  · apply (lt_div_iff₀ Z_pos).mpr
    have scaled := mul_le_mul_of_nonneg_left sine_lower (by positivity : 0 ≤ 2 * s)
    have largest := mul_le_mul_of_nonneg_left Z_upper (by positivity : 0 ≤ 0.92 * b)
    nlinarith only [scaled, base_low, largest, b_pos]
  · apply (div_lt_iff₀ Z_pos).mpr
    have scaled := mul_le_mul_of_nonneg_left (sin_le (by positivity : 0 ≤ d / 2))
      (by positivity : 0 ≤ 2 * s)
    have smallest := mul_lt_mul_of_pos_left Z_lower (by positivity : 0 < 1.01 * b)
    nlinarith only [base_up, scaled, smallest, b_pos]

/-- Correcting the two latitude ordinates preserves their order and leaves
the altitude in the required interval. -/
theorem latitude_chart_height_bounds {r b t Z₀ Z₁ y₀ y₁ : ℝ}
    (r_pos : 0 < r) (r_small : r < 0.116)
    (b_pos : 0 < b) (b_small : b < 0.236 * r)
    (step_lower : 0.963 * (r / 2) < t) (step_upper : t ≤ r / 2)
    (Z₀_lower : 0.998 < Z₀) (Z₀_upper : Z₀ ≤ 1)
    (Z₁_lower : 0.998 < Z₁) (Z₁_upper : Z₁ ≤ 1)
    (north : |y₀ + sin t / Z₀| ≤ 0.251 * b ^ 2 / r)
    (south : |y₁ - sin t / Z₁| ≤ 0.251 * b ^ 2 / r) :
    0.93 * r < y₁ - y₀ ∧ y₁ - y₀ < 1.032 * r := by
  have t_pos : 0 < t := by linarith only [step_lower, r_pos]
  have t_small : t ≤ 0.058 := by linarith only [step_upper, r_small]
  have sine_lower := latitude_sine_at_least t_pos.le t_small
  have sine_pos : 0 < sin t := (mul_pos (by norm_num : (0 : ℝ) < 0.999) t_pos).trans_le sine_lower
  have term (Z : ℝ) (lower : 0.998 < Z) (upper : Z ≤ 1) :
      sin t ≤ sin t / Z ∧ sin t / Z ≤ (r / 2) / 0.998 := by
    have Z_pos : 0 < Z := by linarith only [lower]
    constructor
    · exact (le_div_iff₀ Z_pos).mpr
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left upper sine_pos.le)
    · exact (div_le_div_of_nonneg_right ((sin_le t_pos.le).trans step_upper) Z_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by norm_num) lower.le)
  obtain ⟨lo₀, hi₀⟩ := term Z₀ Z₀_lower Z₀_upper
  obtain ⟨lo₁, hi₁⟩ := term Z₁ Z₁_lower Z₁_upper
  have correction : 0.251 * b ^ 2 / r ≤ 0.014 * r := by
    apply (div_le_iff₀ r_pos).mpr
    have sq := pow_le_pow_left₀ b_pos.le b_small.le 2
    nlinarith only [sq, sq_nonneg r]
  have room : r / 2 / 0.998 = (250 / 499 : ℝ) * r := by ring
  rw [room] at hi₀ hi₁
  obtain ⟨north_lower, north_upper⟩ := abs_le.mp (north.trans correction)
  obtain ⟨south_lower, south_upper⟩ := abs_le.mp (south.trans correction)
  constructor
  · linarith only [step_lower, sine_lower, lo₀, lo₁, north_upper, south_lower, r_pos]
  · linarith only [hi₀, hi₁, north_lower, south_upper, r_pos]

/-- The horizontal variation of a long side is small compared with its actual altitude. -/
theorem latitude_chart_long_side_ratio {r b x y H : ℝ}
    (r_pos : 0 < r) (b_pos : 0 < b) (left : |x| ≤ 0.502 * b)
    (right : |y| ≤ 0.502 * b) (height : 0.93 * r < H) :
    |x - y| / H < 1.08 * b / r := by
  have Hpos : 0 < H := (mul_pos (by norm_num) r_pos).trans height
  have horizontal := (abs_sub x y).trans (add_le_add left right)
  have scale := mul_lt_mul_of_pos_left height (show 0 < 1.08 * b by positivity)
  apply (div_lt_div_iff₀ Hpos r_pos).mpr
  nlinarith only [scale, mul_le_mul_of_nonneg_right horizontal r_pos.le,
    mul_pos b_pos r_pos]

end Unfoldings.FewestNets
