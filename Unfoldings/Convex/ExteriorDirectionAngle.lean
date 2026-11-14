module

public import Unfoldings.Convex.ExteriorProgress

/-! The annular slope ratio bounds every canonically assigned exterior direction. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V)

theorem direction_angle_bound {a b : ℝ} (positive : 0 < a) (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
    (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b) (v : V) :
    InnerProductGeometry.angle (R.slope v) (R.direction (R.slope v)) ≤ Real.arccos (a / b) := by
  have pne : R.slope v ≠ 0 := by
    intro zero
    have norm := E.boundary_norm_ge inner_disk (R.slope_mem_frontier v)
    rw [zero, norm_zero] at norm
    linarith
  have dne : R.direction (R.slope v) ≠ 0 := by
    intro zero
    have norm := R.unit v
    rw [zero, norm_zero] at norm
    norm_num at norm
  apply (angle_le_iff_cos_mul_norm_le pne dne (Real.arccos_nonneg _) (Real.arccos_le_pi _)).mpr
  rw [Real.cos_arccos (by linarith [div_nonneg positive.le bpos.le])
    ((div_le_one bpos).mpr ratio), R.unit, mul_one]
  have bound := mul_le_mul_of_nonneg_left (upper _ (R.active v).1)
    (div_nonneg positive.le bpos.le)
  rw [div_mul_cancel₀ _ bpos.ne'] at bound
  have lower := R.rate_ge positive inner_disk v
  change a ≤ inner ℝ (R.direction (R.slope v)) (R.slope v) at lower
  have comm : inner ℝ (R.direction (R.slope v)) (R.slope v) =
      inner ℝ (R.slope v) (R.direction (R.slope v)) := real_inner_comm _ _
  rw [comm] at lower
  exact bound.trans lower

theorem contact_angle_bound {a b : ℝ} (positive : 0 < a) (bpos : 0 < b) (ratio : a ≤ b)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
    (upper : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {v w : V} (contact : R.Contact v w) :
    InnerProductGeometry.angle (R.slope v) (R.point w - R.point v) ≤ Real.arccos (a / b) := by
  obtain ⟨t, tpos, equal⟩ := contact
  have displacement : R.point w - R.point v = t • R.direction (R.slope v) := by
    rw [equal]
    dsimp [ray]
    abel
  rw [displacement, InnerProductGeometry.angle_smul_right_of_pos _ _ tpos]
  exact R.direction_angle_bound positive bpos ratio inner_disk upper v

theorem contact_inner_progress {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) {v w : V}
    (contact : R.Contact v w) :
    a * ‖R.point w - R.point v‖ ≤ inner ℝ (R.slope v) (R.point w - R.point v) := by
  obtain ⟨t, tpos, equal⟩ := contact
  have displacement : R.point w - R.point v = t • R.direction (R.slope v) := by
    rw [equal]
    dsimp [ray]
    abel
  rw [displacement, norm_smul, R.unit, Real.norm_of_nonneg tpos.le, mul_one,
    real_inner_smul_right]
  have lower := R.rate_ge positive inner_disk v
  change a ≤ inner ℝ (R.direction (R.slope v)) (R.slope v) at lower
  have comm : inner ℝ (R.direction (R.slope v)) (R.slope v) =
      inner ℝ (R.slope v) (R.direction (R.slope v)) := real_inner_comm _ _
  rw [comm] at lower
  nlinarith

end Unfoldings.SlopeEnvelope.ExteriorPlan
