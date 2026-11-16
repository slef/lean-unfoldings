module

public import Unfoldings.Metric.BallIsometry

/-! Whole patch-ball charts retain their canonical maps when the patch is replaced isometrically. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X Y Z : Type*} [EMetricSpace X] [EMetricSpace Y] [EMetricSpace Z]

/-- Replace the actual patch by an isometric mesh, retaining whole-ball coverage and inclusion. -/
theorem exists_ball_chart_isometry_source (e : Z ≃ᵢ X) (f : Z → Y) (y : Y)
    (chart : ∃ source : Z, f source = y ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball y (ENNReal.ofReal r), ∀ z, (B z).val = f z.val) :
    ∃ source : X, f (e.symm source) = y ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball y (ENNReal.ofReal r), ∀ z, (B z).val = f (e.symm z.val) := by
  obtain ⟨source, center, r, rpos, B, agrees⟩ := chart
  let move := basedEBallIsometry e.symm (e source) source
    (e.symm_apply_apply source) (ENNReal.ofReal r)
  refine ⟨e source, (congrArg f (e.symm_apply_apply source)).trans center,
    r, rpos, move.trans B, ?_⟩
  intro z
  exact agrees (move z)

end Unfoldings
