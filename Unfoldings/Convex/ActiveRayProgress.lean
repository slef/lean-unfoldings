module

public import Unfoldings.Convex.SegmentProgress
public import Unfoldings.Convex.CommonPotential

/-! Actual maximizing slopes retain forward progress along every partial piece of a ray. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

/-- An actual active slope at any later ray point has at least the initial forward support. -/
theorem exists_active_along_ray {x p d : Plane} {s : ℝ} (active : E.Active x p)
    (nonnegative : 0 ≤ s) :
    ∃ q, E.Active (x + s • d) q ∧ inner ℝ p d ≤ inner ℝ q d := by
  by_cases zero : s = 0
  · refine ⟨p, ?_, le_rfl⟩
    simpa only [zero, zero_smul, add_zero] using active
  · obtain ⟨q, last⟩ := E.exists_active (x + s • d)
    have monotone := E.active_monotone active last
    have displacement : x + s • d - x = s • d := by abel
    rw [displacement, real_inner_smul_right, inner_sub_left] at monotone
    exact ⟨q, last, by nlinarith [lt_of_le_of_ne nonnegative (Ne.symm zero)]⟩

/-- Every actual forward subsegment has an active initial slope giving the same progress gain. -/
theorem exists_active_ray_segment_progress {x p d : Plane} {c s t : ℝ}
    (active : E.Active x p) (progress : c * ‖d‖ ≤ inner ℝ p d)
    (nonnegative : 0 ≤ s) (ordered : s ≤ t) :
    ∃ q, E.Active (x + s • d) q ∧
      c * ‖(x + t • d) - (x + s • d)‖ ≤
        inner ℝ q ((x + t • d) - (x + s • d)) := by
  obtain ⟨q, active, bound⟩ := E.exists_active_along_ray active nonnegative
  refine ⟨q, active, ?_⟩
  have displacement : (x + t • d) - (x + s • d) = (t - s) • d := by module
  rw [displacement, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ordered), real_inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left (progress.trans bound) (sub_nonneg.mpr ordered)]

/-- Forward support and a norm bound give an angle bound for the actual maximizing slope. -/
theorem active_angle_bound_of_progress {b c : ℝ} (positive : 0 < b) (nonnegative : 0 ≤ c)
    (ratio : c ≤ b) (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    {x p edge : Plane} (active : E.Active x p) (pne : p ≠ 0) (edge_ne : edge ≠ 0)
    (progress : c * ‖edge‖ ≤ inner ℝ p edge) :
    InnerProductGeometry.angle p edge ≤ Real.arccos (c / b) := by
  apply (angle_le_iff_cos_mul_norm_le pne edge_ne (Real.arccos_nonneg _)
    (Real.arccos_le_pi _)).mpr
  rw [Real.cos_arccos (by linarith [div_nonneg nonnegative positive.le])
    ((div_le_one positive).mpr ratio)]
  calc
    _ ≤ (c / b) * (b * ‖edge‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (bounded p active.1) (norm_nonneg _))
      (div_nonneg nonnegative positive.le)
    _ = c * ‖edge‖ := by field_simp
    _ ≤ _ := progress

/-- The same progress coefficient on the incoming history and outgoing edge controls their angle. -/
theorem history_radial_margin_of_active_progress {b c length : ℝ}
    (positive : 0 < b) (nonnegative : 0 ≤ c) (ratio : c ≤ b)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b) {x y p edge : Plane}
    (active : E.Active x p) (pne : p ≠ 0) (different : x ≠ y) (edge_ne : edge ≠ 0)
    (progress : c * length ≤ E.height x - E.height y) (chord : ‖x - y‖ ≤ length)
    (outgoing : c * ‖edge‖ ≤ inner ℝ p edge)
    (small : 2 * Real.arccos (c / b) ≤ Real.pi) :
    Real.cos (2 * Real.arccos (c / b)) * (‖x - y‖ * ‖edge‖) ≤ inner ℝ (x - y) edge := by
  have close := E.active_angle_bound_of_progress positive nonnegative ratio bounded active
    pne edge_ne outgoing
  have margin := E.history_radial_margin positive nonnegative ratio bounded active pne different
    edge_ne progress chord close (Real.arccos_nonneg _) (by linarith)
  simpa only [two_mul] using margin

end Unfoldings.SlopeEnvelope
