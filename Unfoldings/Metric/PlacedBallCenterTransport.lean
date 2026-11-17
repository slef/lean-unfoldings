module

public import Unfoldings.Metric.BallIsometry

/-! Transport an existential physically placed whole-ball chart along a center equality. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X Y S : Type*} [EMetricSpace X] [MetricSpace Y]

/-- Keep the entire original physical chart while changing only its equal named center. -/
theorem exists_placed_ball_chart_of_eq (fold : X → S) (place : Y → S) (condition : Y → Prop)
    {x y : X} (same : x = y)
    (chart : ∃ ε : ℝ, 0 < ε ∧ ∃ a : Y, condition a ∧
      ∃ D : Metric.eball y (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
        ∀ z, place (D z).val = fold z.val) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ a : Y, condition a ∧
      ∃ D : Metric.eball x (ENNReal.ofReal ε) ≃ᵢ Metric.ball a ε,
        ∀ z, place (D z).val = fold z.val := by
  subst y
  exact chart

end Unfoldings
