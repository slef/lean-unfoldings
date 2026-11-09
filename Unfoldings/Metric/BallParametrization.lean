module

public import Unfoldings.Metric.BallChart

/-! Construct a whole metric-ball chart from an isometric parametrization and ball coverage. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X E : Type*} [EMetricSpace X] [MetricSpace E]

theorem HasMetricBallChart.of_isometric_ball {x : X} {p : E} {r : ℝ}
    (positive : 0 < r) (f : Metric.ball p r → X) (isometry : Isometry f)
    (center : f ⟨p, Metric.mem_ball_self positive⟩ = x)
    (covers : ∀ y : X, edist y x < ENNReal.ofReal r → ∃ q, f q = y) :
    HasMetricBallChart E x := by
  let c : Metric.ball p r := ⟨p, Metric.mem_ball_self positive⟩
  have at_center : f c = x := center
  have near (q : Metric.ball p r) : edist (f q) x < ENNReal.ofReal r := by
    rw [← at_center, isometry.edist_eq]
    change edist q.val p < ENNReal.ofReal r
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr (Metric.mem_ball.mp q.property)
  let map (q : Metric.ball p r) : Metric.eball x (ENNReal.ofReal r) := ⟨f q, near q⟩
  have map_isometry : Isometry map := fun q w => isometry q w
  have onto : Function.Surjective map := by
    intro y
    obtain ⟨q, equal⟩ := covers y.val y.property
    exact ⟨q, Subtype.ext equal⟩
  let chart : Metric.ball p r ≃ᵢ Metric.eball x (ENNReal.ofReal r) :=
    ⟨Equiv.ofBijective map ⟨map_isometry.injective, onto⟩, map_isometry⟩
  exact ⟨r, positive, p, ⟨chart.symm⟩⟩

end Unfoldings
