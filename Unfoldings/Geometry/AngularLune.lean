module

public import Unfoldings.Geometry.Azimuth

/-! Exact angular balls describe the two strict half-plane inequalities of a spherical lune. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- On the right half-plane, this angular ball is the indicated unwrapped interval. -/
theorem mem_luneBall_iff {φ θ : ℝ} (principal : |φ| < Real.pi / 2)
    (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi) :
    (φ : Real.Angle) ∈ Metric.ball ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle) (θ / 2) ↔
      φ < θ - Real.pi / 2 := by
  have bounds := abs_lt.mp principal
  have diff_small : |φ - (θ / 2 - Real.pi / 2)| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  have normed : ‖(φ : Real.Angle) - ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle)‖ =
      |φ - (θ / 2 - Real.pi / 2)| := by
    rw [← Real.Angle.coe_sub]
    exact Real.Angle.norm_coe_eq_abs _ diff_small
  rw [Metric.mem_ball, dist_eq_norm, normed, abs_lt]
  constructor
  · intro pair
    linarith [pair.2]
  · intro bound
    constructor <;> linarith

/-- The ball's location ensures its principal argument is in the right half-plane. -/
theorem abs_arg_lt_of_mem_luneBall {w : ℂ} {θ : ℝ} (nonnegative : 0 ≤ θ)
    (small : θ ≤ Real.pi)
    (inside : (w.arg : Real.Angle) ∈
      Metric.ball ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle) (θ / 2)) :
    |w.arg| < Real.pi / 2 := by
  have center_nonpos : θ / 2 - Real.pi / 2 ≤ 0 := by linarith
  have center_small : |θ / 2 - Real.pi / 2| ≤ Real.pi := by
    rw [abs_of_nonpos center_nonpos]
    linarith [Real.pi_pos]
  have center := Real.Angle.norm_coe_eq_abs (θ / 2 - Real.pi / 2) center_small
  rw [abs_of_nonpos center_nonpos] at center
  have principal : ‖(w.arg : Real.Angle)‖ = |w.arg| := by
    rw [Real.Angle.norm_eq_abs_toReal, Complex.arg_coe_angle_toReal_eq_arg]
  have triangle := norm_le_norm_sub_add (w.arg : Real.Angle)
    ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle)
  have near := Metric.mem_ball.mp inside
  rw [dist_eq_norm] at near
  rw [principal, center] at triangle
  linarith

/-- The sign of a rotated horizontal scalar product in this principal interval. -/
theorem rotated_real_neg_iff {w : ℂ} (nonzero : w ≠ 0) {θ : ℝ}
    (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi) (principal : |w.arg| < Real.pi / 2) :
    Real.cos θ * w.re + Real.sin θ * w.im < 0 ↔ w.arg < θ - Real.pi / 2 := by
  have bounds := abs_lt.mp principal
  have formula : Real.cos θ * w.re + Real.sin θ * w.im =
      ‖w‖ * Real.cos (w.arg - θ) := by
    calc
      _ = Real.cos θ * (‖w‖ * Real.cos w.arg) +
          Real.sin θ * (‖w‖ * Real.sin w.arg) := by
        rw [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
      _ = _ := by rw [Real.cos_sub]; ring
  have normpos := norm_pos_iff.mpr nonzero
  have cosine : Real.cos (w.arg - θ) < 0 ↔ w.arg < θ - Real.pi / 2 := by
    constructor
    · intro negative
      by_contra outside
      have interval : w.arg - θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith
      exact (Real.cos_nonneg_of_mem_Icc interval).not_gt negative
    · intro ordered
      rw [← Real.cos_neg (w.arg - θ)]
      apply Real.cos_neg_of_pi_div_two_lt_of_lt
      · linarith
      · linarith
  rw [formula, mul_neg_iff]
  simpa only [normpos, not_lt_of_ge normpos.le, true_and, false_and, or_false] using cosine

/-- A genuine horizontal direction belongs to the lune exactly when both strict signs hold. -/
theorem mem_luneBall_iff_signs {w : ℂ} (nonzero : w ≠ 0) {θ : ℝ}
    (nonnegative : 0 ≤ θ) (small : θ ≤ Real.pi) :
    (w.arg : Real.Angle) ∈ Metric.ball ((θ / 2 - Real.pi / 2 : ℝ) : Real.Angle) (θ / 2) ↔
      0 < w.re ∧ Real.cos θ * w.re + Real.sin θ * w.im < 0 := by
  constructor
  · intro inside
    have principal := abs_arg_lt_of_mem_luneBall nonnegative small inside
    have real : 0 < w.re := by
      rcases Complex.abs_arg_lt_pi_div_two_iff.mp principal with real | zero
      · exact real
      · exact (nonzero zero).elim
    exact ⟨real, (rotated_real_neg_iff nonzero nonnegative small principal).mpr
      ((mem_luneBall_iff principal nonnegative small).mp inside)⟩
  · rintro ⟨real, negative⟩
    have principal := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl real)
    exact (mem_luneBall_iff principal nonnegative small).mpr
      ((rotated_real_neg_iff nonzero nonnegative small principal).mp negative)

end Unfoldings
