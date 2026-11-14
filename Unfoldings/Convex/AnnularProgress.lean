module

public import Unfoldings.Convex.BoundaryPotential
public import Unfoldings.Geometry.AngleConeBound

/-! An inner slope disk turns angular edge choices into uniform potential progress. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem boundary_norm_ge {a : ℝ} (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
    {p : Plane} (boundary : p ∈ frontier E.slopes) : a ≤ ‖p‖ := by
  by_contra small
  have in_ball : p ∈ Metric.ball (0 : Plane) a := by
    simpa only [Metric.mem_ball, dist_zero_right] using (lt_of_not_ge small)
  exact boundary.2 (Metric.isOpen_ball.subset_interior_iff.mpr inner_disk in_ball)

/-- An edge within beta of a slope of norm at least a gains a*cos(beta) per unit length. -/
theorem direction_progress {a β : ℝ} (positive : 0 < a) (beta : 0 ≤ β)
    (acute : β ≤ Real.pi / 2) {p edge : Plane} (lower : a ≤ ‖p‖) (edge_ne : edge ≠ 0)
    (angle : InnerProductGeometry.angle p edge ≤ β) :
    (a * Real.cos β) * ‖edge‖ ≤ inner ℝ p edge := by
  have pne : p ≠ 0 := by intro zero; rw [zero, norm_zero] at lower; linarith
  have scalar := (angle_le_iff_cos_mul_norm_le pne edge_ne beta
    (acute.trans (by linarith [Real.pi_pos]))).mp angle
  have cosine : 0 ≤ Real.cos β :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute⟩
  calc
    _ = Real.cos β * (a * ‖edge‖) := by ring
    _ ≤ Real.cos β * (‖p‖ * ‖edge‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right lower (norm_nonneg _)) cosine
    _ ≤ inner ℝ p edge := scalar

end Unfoldings.SlopeEnvelope
