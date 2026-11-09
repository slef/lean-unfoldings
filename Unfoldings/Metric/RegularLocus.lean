module

public import Unfoldings.Metric.BallChart
public import Unfoldings.Metric.OpenChart

/-! Open isometric charts give whole ball charts, and metric regularity is open. -/

@[expose] public section

open scoped ENNReal Topology

namespace Unfoldings

variable {X E : Type*} [MetricSpace X] [MetricSpace E]

theorem HasMetricBallChart.of_open_chart {D : Set X} {U : Set E}
    (chart : D ≃ᵢ U) (open_D : IsOpen D) (open_U : IsOpen U) (x : D) :
    HasMetricBallChart E x.val := by
  obtain ⟨r, positive, inside, cover⟩ := exists_open_chart_ball_radius chart open_D open_U x
  refine ⟨r, positive, (chart x).val, ?_⟩
  rw [Metric.eball_ofReal]
  exact ⟨restrictChartBall chart x inside cover⟩

theorem isOpen_metric_regular_locus : IsOpen {x : X | HasMetricBallChart E x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x regular
  obtain ⟨D, U, open_D, inside, open_U, ⟨chart⟩⟩ := regular.exists_open_chart
  filter_upwards [open_D.mem_nhds inside] with y hy
  exact HasMetricBallChart.of_open_chart chart open_D open_U ⟨y, hy⟩

end Unfoldings
