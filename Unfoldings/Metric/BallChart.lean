module

public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Metric ball charts

The chart compares the actual ambient distance on a whole open ball with
the distance on an open ball in a named model space. Both openness and the
local isometry are part of this metric condition.
-/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X]

def HasMetricBallChart (E : Type*) [PseudoMetricSpace E] (x : X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ y : E,
    Nonempty (Metric.eball x (ENNReal.ofReal r) ≃ᵢ Metric.ball y r)

theorem HasMetricBallChart.exists_open_chart {E : Type*} [PseudoMetricSpace E]
    {x : X} (regular : HasMetricBallChart E x) :
    ∃ D : Set X, ∃ U : Set E, IsOpen D ∧ x ∈ D ∧ IsOpen U ∧ Nonempty (D ≃ᵢ U) := by
  obtain ⟨r, positive, y, chart⟩ := regular
  exact ⟨Metric.eball x (ENNReal.ofReal r), Metric.ball y r, Metric.isOpen_eball,
    Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive), Metric.isOpen_ball, chart⟩

end Unfoldings
