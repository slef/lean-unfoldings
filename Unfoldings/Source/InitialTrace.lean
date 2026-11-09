module

public import Unfoldings.Source.ChartTrace
public import Unfoldings.Source.ContinuousCoordinates
public import Unfoldings.Source.SampleLine

/-! Construct the initial affine chart trace from the actual source frame. -/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

def coordinateLine (q : SourcePath source) : ℝ →ᵃ[ℝ] Plane :=
  AffineMap.lineMap R.origin (R.coordinate q.path q.geodesic + R.origin)

@[simp] theorem coordinateLine_apply (q : SourcePath source) (t : ℝ) :
    R.coordinateLine q t = t • R.coordinate q.path q.geodesic + R.origin := by
  simp only [coordinateLine, AffineMap.lineMap_apply_module', add_sub_cancel_right]

theorem exists_initial_trace (p : SourcePath source) {δ : unitInterval}
    (before : δ < R.sampleTime p.target) :
    Nonempty (AffineChartTrace p R.coordinateLine 0 δ) := by
  let nearby : Set (SourcePath source) := {q | δ < R.sampleTime q.target}
  have open_nearby : IsOpen nearby :=
    isOpen_lt continuous_const (R.continuous_sampleTime.comp SourcePath.continuous_target)
  have neighborhood : nearby ∈ 𝓝 p := open_nearby.mem_nhds before
  have inside : ∀ q ∈ nearby, ∀ t ∈ Set.Icc (0 : unitInterval) δ,
      q.path t ∈ Metric.eball source (ENNReal.ofReal R.radius) :=
    fun q hq t ht => R.initial_inside q.geodesic t (ht.2.trans hq.le)
  refine ⟨{ domain := Metric.eball source (ENNReal.ofReal R.radius)
            target := Metric.ball R.center R.radius
            open_domain := Metric.isOpen_eball
            open_target := Metric.isOpen_ball
            chart := R.chart
            place := AffineIsometry.id
            nearby := nearby
            neighborhood := neighborhood
            inside := inside
            straight := ?_ }⟩
  intro q hq t ht
  change (R.chart ⟨q.path t, inside q hq t ht⟩).val = R.coordinateLine q (t : ℝ)
  rw [R.coordinateLine_apply]
  exact R.chart_initial_eq q.geodesic t (ht.2.trans hq.le)

end Unfoldings.SourceFrame
