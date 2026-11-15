module

public import Unfoldings.Geometry.RadialMarginSegment

/-! Quantitative radial margins control actual norm increments, without differentiation. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A supporting norm inequality converts an initial radial margin into radial progress. -/
theorem norm_add_sub_norm_ge_radial_margin (x d : E) {γ : ℝ} (small : γ ≤ 1)
    (margin : γ * (‖x‖ * ‖d‖) ≤ inner ℝ x d) :
    γ * ‖d‖ ≤ ‖x + d‖ - ‖x‖ := by
  by_cases zero : x = 0
  · simpa only [zero, zero_add, norm_zero, sub_zero] using
      mul_le_of_le_one_left (norm_nonneg d) small
  · have support := real_inner_le_norm x (x + d)
    rw [inner_add_right, real_inner_self_eq_norm_sq] at support
    have positive := norm_pos_iff.mpr zero
    nlinarith

/-- The same margin holds at every later point of a straight ray in any real inner product space. -/
theorem inner_radial_margin_add_smul (x d : E) {γ t : ℝ} (nonnegative : 0 ≤ γ)
    (small : γ ≤ 1) (time : 0 ≤ t) (margin : γ * (‖x‖ * ‖d‖) ≤ inner ℝ x d) :
    γ * (‖x + t • d‖ * ‖d‖) ≤ inner ℝ (x + t • d) d := by
  have bound : ‖x + t • d‖ ≤ ‖x‖ + t * ‖d‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg time] using norm_add_le x (t • d)
  calc
    _ ≤ γ * ((‖x‖ + t * ‖d‖) * ‖d‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right bound (norm_nonneg d)) nonnegative
    _ = γ * (‖x‖ * ‖d‖) + γ * (t * ‖d‖ ^ 2) := by ring
    _ ≤ inner ℝ x d + t * ‖d‖ ^ 2 :=
      add_le_add margin (mul_le_of_le_one_left (mul_nonneg time (sq_nonneg _)) small)
    _ = _ := by rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Every partial straight edge gains at least its length times the radial margin. -/
theorem norm_ray_progress (x d : E) {γ s t : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (start : 0 ≤ s) (ordered : s ≤ t) (margin : γ * (‖x‖ * ‖d‖) ≤ inner ℝ x d) :
    γ * ‖(t - s) • d‖ ≤ ‖x + t • d‖ - ‖x + s • d‖ := by
  have later := inner_radial_margin_add_smul x d nonnegative small start margin
  have scaled : γ * (‖x + s • d‖ * ‖(t - s) • d‖) ≤
      inner ℝ (x + s • d) ((t - s) • d) := by
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ordered), real_inner_smul_right]
    nlinarith [mul_le_mul_of_nonneg_left later (sub_nonneg.mpr ordered)]
  have progress := norm_add_sub_norm_ge_radial_margin (x + s • d) ((t - s) • d) small scaled
  have equal : x + s • d + (t - s) • d = x + t • d := by module
  rwa [equal] at progress

omit [InnerProductSpace ℝ E] in
/-- Chord progress composes across an actual intermediate point. -/
theorem radial_progress_trans (source x y z : E) {γ : ℝ} (nonnegative : 0 ≤ γ)
    (first : γ * ‖y - x‖ ≤ ‖y - source‖ - ‖x - source‖)
    (last : γ * ‖z - y‖ ≤ ‖z - source‖ - ‖y - source‖) :
    γ * ‖z - x‖ ≤ ‖z - source‖ - ‖x - source‖ := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub z y x
  have scaled := mul_le_mul_of_nonneg_left triangle nonnegative
  nlinarith

end Unfoldings
