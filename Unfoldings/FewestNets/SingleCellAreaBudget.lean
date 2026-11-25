module

public import Unfoldings.FewestNets.ComponentCountBudget
public import Unfoldings.FewestNets.LatitudeMetricRows

/-! The diameter-sensitive residual perimeter estimate gives a common
area-weighted bound for the two single-cell Crofton cases. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- Signed single-cell charges have half the crossing cost of the all-label charge. -/
theorem singleCellCharge_le_area {corners perimeter s t d S A charge : ℝ}
    (corners_nonneg : 0 ≤ corners) (perimeter_nonneg : 0 ≤ perimeter)
    (s_positive : 0 < s) (s_small : s ≤ 1 / 2)
    (sine : 0 < t) (diameter : 0 ≤ d) (area : 0 ≤ A)
    (small_sides : d ≤ 1 → S * d ≤ 4 / (cos (d / 2) ^ 2 * t) * A)
    (large_sides : S * d ≤ 8 / t * A)
    (local_crossings : d < s → charge ≤ corners * (S * d) / (8 * π))
    (all_crossings : s ≤ d → charge ≤ perimeter * S / (8 * π ^ 2)) :
    charge ≤ (2 / (cos (s / 2) ^ 2 * t) * max corners (perimeter / (π * s))) *
      (A / (4 * π)) := by
  have incidence : 0 < sin (π / 2) := by rw [sin_pi_div_two]; norm_num
  have estimate := expectedCharge_le_area corners_nonneg perimeter_nonneg s_positive s_small
    incidence sine diameter area small_sides large_sides (ψ := π) (charge := 2 * charge)
    (fun strict => by
      rw [sin_pi_div_two, div_one]
      have bound := mul_le_mul_of_nonneg_left (local_crossings strict) (by norm_num : (0 : ℝ) ≤ 2)
      convert bound using 1 <;> ring)
    (fun wide => by
      have bound := mul_le_mul_of_nonneg_left (all_crossings wide) (by norm_num : (0 : ℝ) ≤ 2)
      convert bound using 1 <;> ring)
  have scaled : componentCoefficient corners perimeter s π / t * (A / (4 * π)) =
      2 * ((2 / (cos (s / 2) ^ 2 * t) * max corners (perimeter / (π * s))) * (A / (4 * π))) := by
    unfold componentCoefficient
    rw [sin_pi_div_two, div_one]
    ring
  rw [scaled] at estimate
  linarith only [estimate]

/-- The prefactor for input angles at least `2a`, uniformly in `s ≤ 1/2`. -/
theorem latitude_singleCell_prefactor {a s : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6) (s_positive : 0 < s) (s_small : s ≤ 1 / 2) :
    2 / (cos (s / 2) ^ 2 * sin a) ≤ 2.25 / a := by
  have a_lt : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have remainder := abs_sub_sin_le a
  rw [abs_of_pos positive] at remainder
  have square := pow_le_pow_left₀ positive.le a_lt 2
  have cube := mul_le_mul_of_nonneg_left square positive.le
  have sine : 0.95 * a ≤ sin a := by
    nlinarith only [(abs_le.mp remainder).2, cube, positive]
  have s_sq : (s / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [s_small]) 2
  have cos_lower : 31 / 32 ≤ cos (s / 2) :=
    (by linarith only [s_sq, one_sub_sq_div_two_le_cos (x := s / 2)])
  have cos_sq := pow_le_pow_left₀ (show (0 : ℝ) ≤ 31 / 32 by norm_num) cos_lower 2
  have denom_pos : 0 < cos (s / 2) ^ 2 * sin a := by
    have cp : 0 < cos (s / 2) := by linarith only [cos_lower]
    have sp : 0 < sin a := (mul_pos (by norm_num : 0 < (0.95 : ℝ)) positive).trans_le sine
    positivity
  apply (div_le_div_iff₀ denom_pos positive).mpr
  have scaled := mul_le_mul cos_sq sine
    (mul_nonneg (by norm_num) positive.le) (sq_nonneg (cos (s / 2)))
  linarith only [scaled, positive]

/-- Exact scalar corner sum after the three latitude triangle corner estimates. -/
theorem latitude_triangle_corner_sum {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0.639 * (1 / (0.825 * 0.45 * a) + 2 / 0.85) < 2.51 / a := by
  apply (lt_div_iff₀ positive).mpr
  have equal : 0.639 * (1 / (0.825 * 0.45 * a) + 2 / 0.85) * a =
      0.639 * (1 / (0.825 * 0.45) + 2 * a / 0.85) := by
    field_simp [positive.ne'] <;> ring
  rw [equal]
  have bound : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  calc
    _ ≤ 0.639 * (1 / (0.825 * 0.45) + 2 * 0.524 / 0.85) := by gcongr
    _ < (2.51 : ℝ) := by norm_num

end Unfoldings.FewestNets
