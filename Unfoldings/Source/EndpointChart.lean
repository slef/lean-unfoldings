module

public import Unfoldings.Source.TerminalTrace

/-! Extract the actual terminal affine coordinate formula for every nearby shortest path. -/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

theorem exists_endpoint_chart (p : SourcePath source)
    (regular : ∀ t, HasMetricBallChart Plane (p.path t)) :
    ∃ D : Set X, ∃ U : Set Plane, IsOpen D ∧ IsOpen U ∧
      ∃ chart : D ≃ᵢ U, ∃ A : Plane →ᵃⁱ[ℝ] Plane,
        ∃ W : Set (SourcePath source), W ∈ 𝓝 p ∧
          ∃ inside : ∀ q ∈ W, q.target ∈ D, ∀ q (hq : q ∈ W),
            R.coordinate q.path q.geodesic =
              (A (chart ⟨q.target, inside q hq⟩).val) - R.origin := by
  obtain ⟨r, before_end, ⟨trace⟩⟩ := R.exists_terminal_trace p regular
  have inside : ∀ q ∈ trace.nearby, q.target ∈ trace.domain := by
    intro q hq
    have member := trace.inside q hq 1 ⟨before_end.le, le_rfl⟩
    simpa only [Path.target] using member
  refine ⟨trace.domain, trace.target, trace.open_domain, trace.open_target, trace.chart,
    trace.place, trace.nearby, trace.neighborhood, inside, ?_⟩
  intro q hq
  have straight := trace.straight q hq 1 ⟨before_end.le, le_rfl⟩
  have equal : trace.place (trace.chart ⟨q.target, inside q hq⟩).val =
      R.coordinate q.path q.geodesic + R.origin := by
    simpa only [Path.target, R.coordinateLine_apply, Set.Icc.coe_one, one_smul] using straight
  exact eq_sub_iff_add_eq.mpr equal.symm

end Unfoldings.SourceFrame
