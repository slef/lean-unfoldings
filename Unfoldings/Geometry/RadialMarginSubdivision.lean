module

public import Unfoldings.Geometry.RadialMarginSegment

/-! Quantitative radial margins survive every forward subsegment without loss. -/

@[expose] public section

namespace Unfoldings

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Moving the start forward and scaling a directed edge by a nonnegative factor
preserve the original dimensionless radial margin in any real inner product space. -/
theorem radial_margin_forward_piece {r d : V} {γ s scale : ℝ}
    (nonnegative : 0 ≤ γ) (small : γ ≤ 1) (time : 0 ≤ s) (forward : 0 ≤ scale)
    (margin : γ * (‖r‖ * ‖d‖) ≤ inner ℝ r d) :
    γ * (‖r + s • d‖ * ‖scale • d‖) ≤ inner ℝ (r + s • d) (scale • d) := by
  have normbound : ‖r + s • d‖ ≤ ‖r‖ + s * ‖d‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg time] using norm_add_le r (s • d)
  have along : γ * (‖r + s • d‖ * ‖d‖) ≤ inner ℝ (r + s • d) d := by
    calc
      _ ≤ γ * ((‖r‖ + s * ‖d‖) * ‖d‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right normbound (norm_nonneg _)) nonnegative
      _ = γ * (‖r‖ * ‖d‖) + γ * (s * ‖d‖ ^ 2) := by ring
      _ ≤ inner ℝ r d + s * ‖d‖ ^ 2 := add_le_add margin
        (mul_le_of_le_one_left (mul_nonneg time (sq_nonneg _)) small)
      _ = inner ℝ (r + s • d) d := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  calc
    _ = scale * (γ * (‖r + s • d‖ * ‖d‖)) := by
      rw [norm_smul, Real.norm_of_nonneg forward]
      ring
    _ ≤ scale * inner ℝ (r + s • d) d := mul_le_mul_of_nonneg_left along forward
    _ = _ := by rw [real_inner_smul_right]

end Unfoldings
