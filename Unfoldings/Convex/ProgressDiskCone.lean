module

public import Unfoldings.Convex.HistoryCone

/-! A concentric round progress body gives an exact angular cone. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

open InnerProductGeometry Real

/-- The support of the disk in any direction is its radius times the direction's norm. -/
theorem mem_historyCone_closedBall_iff {r : ℝ} (nonneg : 0 ≤ r) (p d : Plane) :
    d ∈ historyCone (Metric.closedBall (0 : Plane) r) p ↔
      r * ‖d‖ ≤ inner ℝ p d := by
  by_cases zero : d = 0
  · simp [zero, historyCone]
  have norm_ne : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr zero
  constructor
  · intro member
    let w := (r / ‖d‖) • d
    have inside : w ∈ Metric.closedBall (0 : Plane) r := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (div_nonneg nonneg (norm_nonneg d)), div_mul_cancel₀ _ norm_ne]
    have bound := member w inside
    change inner ℝ ((r / ‖d‖) • d) d ≤ inner ℝ p d at bound
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two,
      ← mul_assoc, div_mul_cancel₀ _ norm_ne] at bound
    exact bound
  · intro support w inside
    rw [Metric.mem_closedBall, dist_zero_right] at inside
    exact (real_inner_le_norm w d).trans ((mul_le_mul_of_nonneg_right inside (norm_nonneg d)).trans support)

/-- The axis of the disk's history cone is radial. Its half-aperture is
`arccos (r / ‖p‖)`, including a zero aperture on the disk itself. -/
theorem mem_historyCone_closedBall_iff_angle {r : ℝ} (nonneg : 0 ≤ r)
    {p d : Plane} (p_ne : p ≠ 0) (d_ne : d ≠ 0) (radius : r ≤ ‖p‖) :
    d ∈ historyCone (Metric.closedBall (0 : Plane) r) p ↔
      angle p d ≤ arccos (r / ‖p‖) := by
  have p_pos := norm_pos_iff.mpr p_ne
  have ratio_nonneg : 0 ≤ r / ‖p‖ := div_nonneg nonneg p_pos.le
  have ratio_le : r / ‖p‖ ≤ 1 := (div_le_one p_pos).mpr radius
  rw [mem_historyCone_closedBall_iff nonneg,
    angle_le_iff_cos_mul_norm_le p_ne d_ne (arccos_nonneg _) (arccos_le_pi _),
    cos_arccos (by linarith only [ratio_nonneg]) ratio_le,
    ← mul_assoc, div_mul_cancel₀ _ p_pos.ne']

end Unfoldings.SlopeEnvelope
