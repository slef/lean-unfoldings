module

public import Unfoldings.Metric.CenteredChartTransport

/-! Transport a whole local chart along an isometry of its source, retaining the center. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X Y Z : Type*} [EMetricSpace X] [EMetricSpace Y] [EMetricSpace Z]

/-- A source isometry preserves the exact local map on a whole ball at the chosen point. -/
theorem centered_ball_chart_source_isometry (e : X ≃ᵢ Y) (f : Y → Z) (x : X)
    (chart : ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball (e x) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (f (e x)) (ENNReal.ofReal r), ∀ z, (B z).val = f z.val) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (f (e x)) (ENNReal.ofReal r), ∀ z, (B z).val = f (e z.val) := by
  obtain ⟨r, positive, B, agrees⟩ := chart
  let pre := basedEBallIsometry e x (e x) rfl (ENNReal.ofReal r)
  exact ⟨r, positive, pre.trans B, fun z => agrees (pre z)⟩

end Unfoldings
