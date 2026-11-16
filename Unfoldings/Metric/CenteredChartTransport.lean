module

public import Unfoldings.Metric.BallIsometry

/-! Transport whole-ball charts at specified original centers through metric identifications. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X Y X' Y' : Type*} [EMetricSpace X] [EMetricSpace Y]
  [EMetricSpace X'] [EMetricSpace Y']

/-- Source and target isometries preserve a whole chart at the specified source copy. -/
theorem centered_ball_chart_isometries (e : X ≃ᵢ X') (d : Y ≃ᵢ Y') (f : X → Y) (x : X')
    (chart : ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball (e.symm x) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (f (e.symm x)) (ENNReal.ofReal r), ∀ z, (B z).val = f z.val) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (d (f (e.symm x))) (ENNReal.ofReal r),
      ∀ z, (B z).val = d (f (e.symm z.val)) := by
  obtain ⟨r, rpos, B, agrees⟩ := chart
  let pre := basedEBallIsometry e.symm x (e.symm x) rfl (ENNReal.ofReal r)
  let post := basedEBallIsometry d (f (e.symm x)) (d (f (e.symm x))) rfl (ENNReal.ofReal r)
  refine ⟨r, rpos, (pre.trans B).trans post, ?_⟩
  intro z
  exact congrArg d (agrees (pre z))

end Unfoldings
