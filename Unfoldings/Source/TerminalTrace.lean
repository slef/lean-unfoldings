module

public import Unfoldings.Source.InitialTrace
public import Unfoldings.Path.ChartPartition

/-!
# Constructing straight source coordinates through a regular reference path

Choose a finite strictly ordered chart partition of the actual reference path.
The source frame constructs the first trace. The proved transition step then
continues it through every chart, retaining a neighborhood of the whole path
space at each finite step. The terminal trace is a theorem, not input data.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] {source : X} (R : SourceFrame source)

theorem exists_terminal_trace (p : SourcePath source)
    (regular : ∀ t, HasMetricBallChart Plane (p.path t)) :
    ∃ r : unitInterval, r < 1 ∧ Nonempty (AffineChartTrace p R.coordinateLine r 1) := by
  obtain ⟨P⟩ := exists_metricChartPartition Plane p.path regular
  have steps_pos : 0 < P.steps := MetricChartPartition.steps_pos Plane P
  let first : Fin (P.steps + 1) := ⟨1, by omega⟩
  let i₀ : Fin P.steps := ⟨0, steps_pos⟩
  have first_pos : (0 : unitInterval) < P.time first := by
    calc
      0 = P.time 0 := P.start.symm
      _ < P.time first := P.increasing (by change (0 : ℕ) < 1; omega)
  obtain ⟨δ, δpos, δsmall⟩ := exists_between (lt_min (R.sampleTime_pos p.target) first_pos)
  have δsample : δ < R.sampleTime p.target := δsmall.trans_le (min_le_left _ _)
  have δfirst : δ < P.time first := δsmall.trans_le (min_le_right _ _)
  obtain ⟨initial⟩ := R.exists_initial_trace p δsample
  have first_inside : ∀ v ∈ Set.Icc δ (P.time first), p.path v ∈ P.domain i₀ := by
    intro v hv
    apply P.inside i₀ v
    constructor
    · change P.time 0 ≤ v
      rw [P.start]
      exact δpos.le.trans hv.1
    · exact hv.2
  obtain ⟨first_trace⟩ := initial.extend δpos δfirst (P.chart i₀) (P.open_domain i₀)
    (P.open_target i₀) first_inside
  have advance : ∀ (k : ℕ), 1 ≤ k → ∀ bound : k ≤ P.steps,
      ∃ r : unitInterval, r < P.time ⟨k, Nat.lt_succ_of_le bound⟩ ∧
        Nonempty (AffineChartTrace p R.coordinateLine r (P.time ⟨k, Nat.lt_succ_of_le bound⟩)) := by
    intro k
    induction k with
    | zero => intro positive _bound; omega
    | succ k ih =>
      intro _positive bound
      by_cases zero : k = 0
      · subst k
        exact ⟨δ, δfirst, ⟨first_trace⟩⟩
      · have kpos : 1 ≤ k := by omega
        have previous_bound : k ≤ P.steps := by omega
        obtain ⟨r, ordered, ⟨old⟩⟩ := ih kpos previous_bound
        let i : Fin P.steps := ⟨k, by omega⟩
        have next_ordered : P.time ⟨k, Nat.lt_succ_of_le previous_bound⟩ <
            P.time ⟨k + 1, Nat.lt_succ_of_le bound⟩ :=
          P.increasing (by change k < k + 1; omega)
        have next_inside : ∀ v ∈ Set.Icc
            (P.time ⟨k, Nat.lt_succ_of_le previous_bound⟩)
            (P.time ⟨k + 1, Nat.lt_succ_of_le bound⟩), p.path v ∈ P.domain i :=
          fun v hv => P.inside i v hv
        obtain ⟨next⟩ := old.extend ordered next_ordered (P.chart i)
          (P.open_domain i) (P.open_target i) next_inside
        exact ⟨P.time ⟨k, Nat.lt_succ_of_le previous_bound⟩, next_ordered, ⟨next⟩⟩
  obtain ⟨r, before, trace⟩ := advance P.steps steps_pos le_rfl
  change r < P.time (Fin.last P.steps) at before
  change Nonempty (AffineChartTrace p R.coordinateLine r (P.time (Fin.last P.steps))) at trace
  rw [P.finish] at before trace
  exact ⟨r, before, trace⟩

end Unfoldings.SourceFrame
