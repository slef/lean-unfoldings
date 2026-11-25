module

public import Unfoldings.FewestNets.AcuteLatitudeMetricRows
public import Unfoldings.FewestNets.AcuteLatitudeVertexBounds

/-! Base length and signed altitude in the acute latitude triangle charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- With the two base sites equally spaced about the midpoint, their
gnomonic horizontal separation has the claimed quantitative base length. -/
theorem chart_base_bounds {r b s d Z : ℝ}
    (r_pos : 0 < r) (b_pos : 0 < b) (b_small : b < 0.294 * r)
    (s_lower : (0.999 / 3.864) * r < s) (Z_lower : 0.991 < Z) (Z_upper : Z ≤ 1)
    (spacing_lower : b / (1.182 * s) < d) (spacing_upper : d ≤ b / s) :
    0.8 * b < 2 * s * sin (d / 2) / Z ∧ 2 * s * sin (d / 2) / Z < 1.010 * b := by
  have s_pos : 0 < s := by linarith only [r_pos, s_lower]
  have Z_pos : 0 < Z := by linarith only [Z_lower]
  have d_pos : 0 < d := (div_pos b_pos (by positivity : (0 : ℝ) < 1.182 * s)).trans spacing_lower
  have base_low := (div_lt_iff₀ (by positivity : (0 : ℝ) < 1.182 * s)).mp spacing_lower
  have base_up := (le_div_iff₀ s_pos).mp spacing_upper
  have h_upper : d / 2 < 0.569 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have b_bound : b < 1.138 * s := by linarith only [s_lower, r_pos, b_small]
    have d_bound := (mul_lt_mul_iff_of_pos_right s_pos).mp (base_up.trans_lt b_bound)
    linarith only [d_bound]
  have sine_lower : 0.946 * (d / 2) ≤ sin (d / 2) := by
    have rem := abs_sub_sin_le (d / 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ d / 2)] at rem
    have square := pow_le_pow_left₀ (by positivity : 0 ≤ d / 2) h_upper.le 2
    have cube := mul_le_mul_of_nonneg_right square (by positivity : 0 ≤ d / 2)
    nlinarith only [(abs_le.mp rem).2, cube, d_pos]
  constructor
  · apply (lt_div_iff₀ Z_pos).mpr
    have scaled := mul_le_mul_of_nonneg_left sine_lower (by positivity : 0 ≤ 2 * s)
    have largest := mul_le_mul_of_nonneg_left Z_upper (by positivity : 0 ≤ 0.8 * b)
    nlinarith only [scaled, base_low, largest, b_pos]
  · apply (div_lt_iff₀ Z_pos).mpr
    have scaled := mul_le_mul_of_nonneg_left (sin_le (by positivity : 0 ≤ d / 2))
      (by positivity : 0 ≤ 2 * s)
    have smallest := mul_lt_mul_of_pos_left Z_lower (by positivity : 0 < 1.010 * b)
    nlinarith only [base_up, scaled, smallest, b_pos]

/-- The horizontal variation of a long side is small compared with its actual altitude. -/
theorem chart_long_side_ratio {r b x y H : ℝ}
    (r_pos : 0 < r) (b_pos : 0 < b) (left : |x| ≤ 0.505 * b)
    (right : |y| ≤ 0.505 * b) (height : 0.883 * r < H) :
    |x - y| / H < 1.144 * b / r := by
  have Hpos : 0 < H := (mul_pos (by norm_num) r_pos).trans height
  have horizontal := (abs_sub x y).trans (add_le_add left right)
  have scale := mul_lt_mul_of_pos_left height (show 0 < 1.144 * b by positivity)
  apply (div_lt_div_iff₀ Hpos r_pos).mpr
  nlinarith only [scale, mul_le_mul_of_nonneg_right horizontal r_pos.le,
    mul_pos b_pos r_pos]

/-- The two ordinate corrections have the same weak sign, so only one correction
budget is needed for the height between the two rows. -/
theorem chart_height_bounds {r b ell t w₀ w₁ : ℝ}
    (r_pos : 0 < r) (r_small : r < 0.234)
    (b_pos : 0 < b) (b_small : b < 0.294 * r)
    (step_lower : 0.928 * (r / 2) < t) (step_upper : t ≤ r / 2)
    (north_sine : 0 ≤ sin (ell - t)) (south_sine : 0 ≤ sin (ell + t)) :
    let Z₀ := latitudeDenominator ell (ell - t) w₀
    let Z₁ := latitudeDenominator ell (ell + t) w₁
    let e₀ := -(cos ell * sin (ell - t) * (1 - cos w₀)) / Z₀
    let e₁ := -(cos ell * sin (ell + t) * (1 - cos w₁)) / Z₁
    0.991 < Z₀ → Z₀ ≤ 1 → 0.991 < Z₁ → Z₁ ≤ 1 →
    |e₀| ≤ 0.489 * b ^ 2 / r → |e₁| ≤ 0.489 * b ^ 2 / r →
    0.883 * r < sin t / Z₁ + e₁ - (-sin t / Z₀ + e₀) ∧
      sin t / Z₁ + e₁ - (-sin t / Z₀ + e₀) < 1.052 * r := by
  intro Z₀ Z₁ e₀ e₁ Z₀_lower Z₀_upper Z₁_lower Z₁_upper north south
  have t_pos : 0 < t := by linarith only [step_lower, r_pos]
  have t_small : t ≤ 0.117 := by linarith only [step_upper, r_small]
  have sine_lower : 0.9977 * t ≤ sin t := by
    have remainder := abs_sub_sin_le t
    rw [abs_of_pos t_pos] at remainder
    have square := pow_le_pow_left₀ t_pos.le t_small 2
    have cube := mul_le_mul_of_nonneg_right square t_pos.le
    nlinarith only [(abs_le.mp remainder).2, cube, t_pos]
  have sine_pos : 0 < sin t := (mul_pos (by norm_num : (0 : ℝ) < 0.9977) t_pos).trans_le sine_lower
  have term (Z : ℝ) (lower : 0.991 < Z) (upper : Z ≤ 1) :
      sin t ≤ sin t / Z ∧ sin t / Z ≤ (500 / 991 : ℝ) * r := by
    have Z_pos : 0 < Z := by linarith only [lower]
    constructor
    · exact (le_div_iff₀ Z_pos).mpr
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left upper sine_pos.le)
    · calc
        _ ≤ (r / 2) / Z := div_le_div_of_nonneg_right
          ((sin_le t_pos.le).trans step_upper) Z_pos.le
        _ ≤ (r / 2) / 0.991 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) lower.le
        _ = _ := by ring
  obtain ⟨lo₀, hi₀⟩ := term Z₀ Z₀_lower Z₀_upper
  obtain ⟨lo₁, hi₁⟩ := term Z₁ Z₁_lower Z₁_upper
  have correction : 0.489 * b ^ 2 / r ≤ 0.04227 * r := by
    apply (div_le_iff₀ r_pos).mpr
    have sq := pow_le_pow_left₀ b_pos.le b_small.le 2
    nlinarith only [sq, sq_nonneg r]
  obtain ⟨north_lower, north_upper⟩ := abs_le.mp (north.trans correction)
  obtain ⟨south_lower, south_upper⟩ := abs_le.mp (south.trans correction)
  have same_sign : (0 ≤ e₀ ∧ 0 ≤ e₁) ∨ (e₀ ≤ 0 ∧ e₁ ≤ 0) := by
    have drop₀ := sub_nonneg.mpr (cos_le_one w₀)
    have drop₁ := sub_nonneg.mpr (cos_le_one w₁)
    have Z₀_pos : 0 < Z₀ := by linarith only [Z₀_lower]
    have Z₁_pos : 0 < Z₁ := by linarith only [Z₁_lower]
    by_cases hc : 0 ≤ cos ell
    · right
      exact ⟨div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
        (mul_nonneg (mul_nonneg hc north_sine) drop₀)) Z₀_pos.le,
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
          (mul_nonneg (mul_nonneg hc south_sine) drop₁)) Z₁_pos.le⟩
    · left
      have hc' := (le_of_not_ge hc)
      exact ⟨div_nonneg (neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' north_sine) drop₀))
        Z₀_pos.le,
        div_nonneg (neg_nonneg.mpr
          (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc' south_sine) drop₁))
          Z₁_pos.le⟩
  have step : 0.9977 * (0.928 * (r / 2)) < sin t :=
    (mul_lt_mul_of_pos_left step_lower (by norm_num)).trans_le sine_lower
  rw [neg_div]
  rcases same_sign with ⟨sign₀, sign₁⟩ | ⟨sign₀, sign₁⟩
  · constructor
    · linarith only [step, lo₀, lo₁, north_upper, sign₁, r_pos]
    · linarith only [hi₀, hi₁, sign₀, south_upper, r_pos]
  · constructor
    · linarith only [step, lo₀, lo₁, sign₀, south_lower, r_pos]
    · linarith only [hi₀, hi₁, north_lower, sign₁, r_pos]

end Unfoldings.FewestNets.AcuteLatitudeGrid
