module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith

/-! Small angular error and small relative length expansion give uniform vector error. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sub_sq_le_of_angle_norm_bounds {δ : ℝ} (nonnegative : 0 ≤ δ)
    (small : δ ≤ Real.pi / 2) (u v : E) (lower : ‖v‖ ≤ ‖u‖)
    (upper : ‖u‖ ≤ (1 + δ) * ‖v‖) (angle : InnerProductGeometry.angle u v ≤ δ) :
    ‖u - v‖ ^ 2 ≤ ((1 + δ) ^ 2 + 1 - 2 * Real.cos δ) * ‖v‖ ^ 2 := by
  have cos_nonnegative := Real.cos_nonneg_of_mem_Icc
    (show δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], small⟩)
  have cos_bound := Real.cos_le_cos_of_nonneg_of_le_pi
    (InnerProductGeometry.angle_nonneg u v) (small.trans (by linarith [Real.pi_pos])) angle
  have product_bound : ‖v‖ ^ 2 ≤ ‖u‖ * ‖v‖ := by
    nlinarith [mul_le_mul_of_nonneg_right lower (norm_nonneg v)]
  have inner_bound : Real.cos δ * ‖v‖ ^ 2 ≤ inner ℝ u v := by
    calc
      _ ≤ Real.cos δ * (‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left product_bound cos_nonnegative
      _ ≤ Real.cos (InnerProductGeometry.angle u v) * (‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right cos_bound (mul_nonneg (norm_nonneg u) (norm_nonneg v))
      _ = _ := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
  have square_bound : ‖u‖ ^ 2 ≤ ((1 + δ) * ‖v‖) ^ 2 :=
    by simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg u) upper
  rw [norm_sub_sq_real]
  nlinarith

/-- The tolerance is numerical and independent of dimension, vectors, cap, or triangulation. -/
theorem exists_angle_norm_error_threshold {ε : ℝ} (positive : 0 < ε) :
    ∃ δ > 0, ∀ u v : E, ‖v‖ ≤ ‖u‖ → ‖u‖ ≤ (1 + δ) * ‖v‖ →
      InnerProductGeometry.angle u v ≤ δ → ‖u - v‖ ≤ ε * ‖v‖ := by
  let g := fun d : ℝ => (1 + d) ^ 2 + 1 - 2 * Real.cos d
  have continuous : Continuous g :=
    (((continuous_const.add continuous_id).pow 2).add continuous_const).sub
      (continuous_const.mul Real.continuous_cos)
  have near : ∀ᶠ d in 𝓝 (0 : ℝ), g d < ε ^ 2 :=
    continuous.continuousAt.eventually (Iio_mem_nhds (by
      norm_num only [g, add_zero, one_pow, Real.cos_zero, mul_one, one_add_one_eq_two,
        sub_self]
      exact sq_pos_of_pos positive))
  obtain ⟨r, rpositive, within⟩ := Metric.eventually_nhds_iff.mp near
  let δ := min (r / 2) (Real.pi / 4)
  have δpositive : 0 < δ := lt_min (by positivity) (by positivity)
  have δsmall : δ ≤ Real.pi / 2 := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have estimate : g δ < ε ^ 2 := within (by
    rw [Real.dist_eq, sub_zero, abs_of_pos δpositive]
    exact (min_le_left _ _).trans_lt (by linarith))
  refine ⟨δ, δpositive, fun u v lower upper angle => ?_⟩
  have square := norm_sub_sq_le_of_angle_norm_bounds δpositive.le δsmall u v lower upper angle
  have scale_bound := mul_le_mul_of_nonneg_right estimate.le (sq_nonneg ‖v‖)
  change g δ * ‖v‖ ^ 2 ≤ ε ^ 2 * ‖v‖ ^ 2 at scale_bound
  have result : ‖u - v‖ ^ 2 ≤ (ε * ‖v‖) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg positive.le (norm_nonneg v))).mp result

end Unfoldings
