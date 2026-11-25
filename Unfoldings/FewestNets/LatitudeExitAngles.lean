module

public import Unfoldings.FewestNets.LatitudeTriangleShape
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The signed long-side slopes give both the three-exit windows and a lower bound on the apex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- On the actual range of the two side ratios, arctangent has derivative
between 0.938 and 1. -/
theorem latitude_arctan_difference {u v : ℝ} (ordered : u < v) (lo : |u| ≤ 0.255)
    (hi : |v| ≤ 0.255) :
    0.938 * (v - u) ≤ arctan v - arctan u ∧ arctan v - arctan u ≤ v - u := by
  obtain ⟨c, member, slope⟩ := exists_deriv_eq_slope arctan ordered
    continuous_arctan.continuousOn differentiable_arctan.differentiableOn
  rw [Real.deriv_arctan] at slope
  change 1 / (1 + c ^ 2) = (arctan v - arctan u) / (v - u) at slope
  have close : |c| ≤ 0.255 := abs_le.mpr
    ⟨((abs_le.mp lo).1).trans member.1.le, member.2.le.trans (abs_le.mp hi).2⟩
  have square := pow_le_pow_left₀ (abs_nonneg c) close 2
  rw [sq_abs] at square
  have den_pos : 0 < 1 + c ^ 2 := by positivity
  have bottom : 0.938 ≤ 1 / (1 + c ^ 2) := (le_div_iff₀ den_pos).mpr (by linarith only [square])
  have top : 1 / (1 + c ^ 2) ≤ 1 :=
    (div_le_one₀ den_pos).mpr (by linarith only [sq_nonneg c])
  rw [slope] at bottom top
  exact ⟨(le_div_iff₀ (sub_pos.mpr ordered)).mp bottom,
    (div_le_iff₀ (sub_pos.mpr ordered)).mp top |>.trans_eq (one_mul _)⟩

/-- The signed east and west deviations from horizontal have all three
required margins. Their difference is also the planar apex angle. -/
theorem latitude_exit_margins_of_side_ratios {a r b H B u v : ℝ}
    (positive : 0 < a) (r_pos : 0 < r) (spacing : b = 0.45 * a * r)
    (b_small : b < 0.236 * r)
    (H_low : 0.93 * r < H) (H_up : H < 1.032 * r)
    (B_low : 0.92 * b < B) (B_up : B < 1.01 * b)
    (east : |u| < 1.08 * b / r) (west : |v| < 1.08 * b / r)
    (ratios : v - u = B / H) :
    let e := arctan u
    let w := arctan v
    |e| < 0.99 * a ∧ |w| < 0.99 * a ∧
      0.235 * a < 0.495 * a + e / 2 ∧ 0.235 * a < 0.495 * a - w / 2 ∧
      0.235 * a < 0.99 * a + e - w ∧ 0.835 * b / r < w - e := by
  have b_pos : 0 < b := by rw [spacing]; positivity
  have H_pos : 0 < H := (mul_pos (by norm_num) r_pos).trans H_low
  have B_pos : 0 < B := (mul_pos (by norm_num) b_pos).trans B_low
  have gap : u < v := sub_pos.mp (ratios.symm ▸ div_pos B_pos H_pos)
  have cap : 1.08 * b / r ≤ 0.255 := by
    apply (div_le_iff₀ r_pos).mpr
    linarith only [b_small, r_pos]
  have ⟨diff_lower, diff_upper⟩ := latitude_arctan_difference gap (east.le.trans cap)
    (west.le.trans cap)
  rw [ratios] at diff_lower diff_upper
  have spread : B / H < 0.489 * a := by
    apply (div_lt_iff₀ H_pos).mpr
    have scaled := mul_lt_mul_of_pos_left H_low (show 0 < 0.489 * a by positivity)
    rw [spacing] at B_up
    nlinarith only [B_up, scaled, mul_pos positive r_pos]
  have separation : 0.891 * b / r < B / H := by
    apply (div_lt_div_iff₀ r_pos H_pos).mpr
    have upper := mul_lt_mul_of_pos_left H_up (show 0 < 0.891 * b by positivity)
    have lower := mul_lt_mul_of_pos_right B_low r_pos
    nlinarith only [upper, lower, mul_pos b_pos r_pos]
  have magnitude : 1.08 * b / r = 0.486 * a := by
    rw [spacing]
    field_simp [r_pos.ne'] <;> ring
  have e_close := abs_arctan_le_abs.trans_lt east
  have w_close := abs_arctan_le_abs.trans_lt west
  rw [magnitude] at e_close w_close
  dsimp only
  refine ⟨e_close.trans (by linarith only [positive]), w_close.trans (by linarith only [positive]),
    ?_, ?_, ?_, ?_⟩
  · linarith only [(abs_lt.mp e_close).1, positive]
  · linarith only [(abs_lt.mp w_close).2, positive]
  · linarith only [diff_upper, spread, positive]
  · have enough := mul_lt_mul_of_pos_left separation (show (0 : ℝ) < 0.938 by norm_num)
    have factor : 0.938 * (0.891 * b / r) = (0.938 * 0.891) * (b / r) := by ring
    rw [factor] at enough
    rw [mul_div_assoc]
    linarith only [enough, diff_lower, div_pos b_pos r_pos]

end Unfoldings.FewestNets
