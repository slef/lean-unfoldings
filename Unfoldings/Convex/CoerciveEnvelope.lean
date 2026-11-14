module

public import Unfoldings.Convex.SlopeEnvelope
public import Mathlib.Analysis.Convex.Topology

/-! An inner slope disk makes the conjugate coercive and all of its sublevel sets compact. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem exists_coercive_bound {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) :
    ∃ D : ℝ, ∀ x : Plane, a * ‖x‖ ≤ E.height x + D := by
  have closed_disk : Metric.closedBall (0 : Plane) a ⊆ E.slopes := by
    rw [← closure_ball (0 : Plane) positive.ne']
    exact closure_minimal inner_disk E.compact.isClosed
  obtain ⟨q, hq, maximum⟩ := E.compact.exists_isMaxOn E.nonempty E.continuous_dual.continuousOn
  refine ⟨E.dual q, ?_⟩
  intro x
  by_cases zero : x = 0
  · subst x
    have member : (0 : Plane) ∈ E.slopes := inner_disk (Metric.mem_ball_self positive)
    have lower := E.affine_le 0 member
    have bound := maximum member
    change E.dual 0 ≤ E.dual q at bound
    simp only [affine, inner_zero_left, zero_sub, norm_zero, mul_zero] at lower ⊢
    linarith
  · let p := (a / ‖x‖) • x
    have normp : ‖p‖ = a := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg positive.le (norm_nonneg _))]
      exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr zero)
    have member : p ∈ E.slopes := by
      apply closed_disk
      simpa only [Metric.mem_closedBall, dist_zero_right, normp] using le_refl a
    have lower := E.affine_le x member
    have bound := maximum member
    change E.dual p ≤ E.dual q at bound
    have pairing : inner ℝ x p = a * ‖x‖ := by
      change inner ℝ x ((a / ‖x‖) • x) = _
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    dsimp only [affine] at lower
    rw [pairing] at lower
    linarith

theorem compact_sublevel {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) (r : ℝ) :
    IsCompact {x | E.height x ≤ r} := by
  obtain ⟨D, bound⟩ := E.exists_coercive_bound positive inner_disk
  have closed : IsClosed {x | E.height x ≤ r} := isClosed_le E.continuous_height continuous_const
  have bounded : Bornology.IsBounded {x | E.height x ≤ r} := by
    apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := (r + D) / a)).subset
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ positive]
    have lower := bound x
    change E.height x ≤ r at hx
    nlinarith
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨closed, bounded⟩

end Unfoldings.SlopeEnvelope
