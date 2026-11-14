module

public import Unfoldings.Convex.SlopeEnvelope
public import Mathlib.Tactic.Module

/-! Local common-potential progress persists between arbitrary points on an oriented edge. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem active_monotone {x y p q : Plane} (first : E.Active x p) (last : E.Active y q) :
    0 ≤ inner ℝ (q - p) (y - x) := by
  have one := E.active_support first y
  have two := E.active_support last x
  have reversed : x - y = -(y - x) := by abel
  rw [reversed, inner_neg_right] at one
  rw [inner_sub_left]
  linarith

/-- A supporting slope chosen at the start controls every later subsegment, even if the
potential changes active slope along the edge. No endpoint-only inference is used. -/
theorem ray_segment_progress {x p d : Plane} {c s t : ℝ} (active : E.Active x p)
    (step : c * ‖d‖ ≤ inner ℝ p d) (snonnegative : 0 ≤ s) (ordered : s ≤ t) :
    c * ‖(x + t • d) - (x + s • d)‖ ≤
      E.height (x + t • d) - E.height (x + s • d) := by
  have at_s : ∃ q, E.Active (x + s • d) q ∧ inner ℝ p d ≤ inner ℝ q d := by
    by_cases zero : s = 0
    · refine ⟨p, ?_, le_rfl⟩
      simpa only [zero, zero_smul, add_zero] using active
    · obtain ⟨q, last⟩ := E.exists_active (x + s • d)
      have monotone := E.active_monotone active last
      have displacement : x + s • d - x = s • d := by abel
      rw [displacement, real_inner_smul_right, inner_sub_left] at monotone
      exact ⟨q, last, by nlinarith [lt_of_le_of_ne snonnegative (Ne.symm zero)]⟩
  obtain ⟨q, last, direction⟩ := at_s
  have support := E.active_support last (x + t • d)
  have forward : (x + t • d) - (x + s • d) = (t - s) • d := by module
  have backward : (x + s • d) - (x + t • d) = (s - t) • d := by module
  rw [backward, real_inner_smul_right] at support
  calc
    _ = (t - s) * (c * ‖d‖) := by
      rw [forward, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ordered)]
      ring
    _ ≤ (t - s) * inner ℝ q d :=
      mul_le_mul_of_nonneg_left (step.trans direction) (sub_nonneg.mpr ordered)
    _ ≤ E.height (x + t • d) - E.height (x + s • d) := by nlinarith

end Unfoldings.SlopeEnvelope
