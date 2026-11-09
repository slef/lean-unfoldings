module

public import Unfoldings.Metric.RegularLocus
public import Unfoldings.Topology.FiniteIntervalCover
public import Mathlib.Topology.Path

/-!
# Finite strictly ordered chart partitions of regular paths

The actual open chart cover first gives a monotone finite subdivision by
Mathlib's Lebesgue-number theorem. Sorting the resulting closed intervals'
endpoints removes every degenerate interval. Each remaining whole path piece
lies in one actual open isometric chart.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X] (E : Type*) [MetricSpace E]
  {a b : X}

structure MetricChartPartition (p : Path a b) where
  steps : ℕ
  time : Fin (steps + 1) → unitInterval
  increasing : StrictMono time
  start : time 0 = 0
  finish : time (Fin.last steps) = 1
  domain : Fin steps → Set X
  target : Fin steps → Set E
  open_domain : ∀ i, IsOpen (domain i)
  open_target : ∀ i, IsOpen (target i)
  chart : ∀ i, domain i ≃ᵢ target i
  inside : ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ), p t ∈ domain i

theorem MetricChartPartition.steps_pos {p : Path a b} (P : MetricChartPartition E p) :
    0 < P.steps := by
  by_contra wrong
  have zero : P.steps = 0 := Nat.eq_zero_of_not_pos wrong
  have last : Fin.last P.steps = 0 := by
    apply Fin.ext
    simpa only [Fin.val_last, Fin.val_zero] using zero
  have equal := P.finish
  rw [last, P.start] at equal
  exact zero_ne_one equal

theorem exists_metricChartPartition (p : Path a b)
    (regular : ∀ t, HasMetricBallChart E (p t)) : Nonempty (MetricChartPartition E p) := by
  classical
  have charts (t : unitInterval) := (regular t).exists_open_chart
  choose D U open_D at_t open_U charts using charts
  let chart (t : unitInterval) : D t ≃ᵢ U t := Classical.choice (charts t)
  let c (t : unitInterval) := p ⁻¹' D t
  have open_c (t : unitInterval) : IsOpen (c t) := (open_D t).preimage p.continuous
  have cover : Set.univ ⊆ ⋃ t, c t := by
    intro t _
    exact Set.mem_iUnion.mpr ⟨t, at_t t⟩
  obtain ⟨time, start, _monotone, ⟨N, ends⟩, pieces⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval open_c cover
  have cover_aux (n : ℕ) : ∀ v : unitInterval, v ≤ time (n + 1) →
      ∃ i : Fin (n + 1), time i.val ≤ v ∧ v ≤ time (i.val + 1) := by
    induction n with
    | zero =>
      intro v hv
      refine ⟨0, ?_, hv⟩
      change time 0 ≤ v
      rw [start]
      exact v.property.1
    | succ n ih =>
      intro v hv
      by_cases before : v ≤ time (n + 1)
      · obtain ⟨i, first, last⟩ := ih v before
        exact ⟨i.castSucc, first, last⟩
      · exact ⟨Fin.last (n + 1), le_of_not_ge before, hv⟩
  let lower (i : Fin (N + 1)) := time i.val
  let upper (i : Fin (N + 1)) := time (i.val + 1)
  have closed_cover (v : unitInterval) : ∃ i, lower i ≤ v ∧ v ≤ upper i :=
    cover_aux N v (by rw [ends (N + 1) (by omega)]; exact v.property.2)
  obtain ⟨n, _bound, grid, increasing, first, last, piece, contained⟩ :=
    exists_finite_interval_subdivision lower upper closed_cover
  choose label covers using fun i : Fin (N + 1) => pieces i.val
  refine ⟨{ steps := n
            time := grid
            increasing := increasing
            start := first
            finish := last
            domain := fun i => D (label (piece i))
            target := fun i => U (label (piece i))
            open_domain := fun i => open_D (label (piece i))
            open_target := fun i => open_U (label (piece i))
            chart := fun i => chart (label (piece i))
            inside := ?_ }⟩
  intro i t ht
  exact covers (piece i) (contained i ht)

end Unfoldings
