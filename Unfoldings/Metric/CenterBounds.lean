module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.Ring

/-!
# Distance bounds from local center bounds

A bound from each center extends along a real interval by continuous induction.
This adapts the generic continuous-induction argument from
slef/EdgeUnfoldings, Geometry/IntervalCenterBound, without its finite-selection
dependency or any unfolding hypotheses.
-/

@[expose] public section

open Set Filter Topology

namespace Unfoldings

/-- Bounds from nearby centers add up to the same bound between interval endpoints. -/
theorem interval_distance_of_center_bounds {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) (a b K : ℝ) (ordered : a ≤ b)
    (continuous_f : ContinuousOn f (Icc a b))
    (local_bound : ∀ x ∈ Icc a b, ∀ᶠ y in 𝓝[Icc a b] x,
      dist (f y) (f x) ≤ K * dist y x) :
    dist (f a) (f b) ≤ K * (b - a) := by
  let good : Set ℝ := {t | dist (f a) (f t) ≤ K * (t - a)}
  have closed : IsClosed (good ∩ Icc a b) := by
    rw [inter_comm]
    exact isClosed_Icc.isClosed_le
      ((continuous_const.dist continuous_id).comp_continuousOn continuous_f)
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
  have start : a ∈ good := by simp [good]
  have all_good := closed.Icc_subset_of_forall_mem_nhdsWithin start (fun x hx => ?_)
  · exact all_good ⟨ordered, le_rfl⟩
  · have near := (local_bound x ⟨hx.2.1, hx.2.2.le⟩).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx.2))
    filter_upwards [near, self_mem_nhdsWithin] with y hy xy
    change x < y at xy
    change dist (f a) (f y) ≤ K * (y - a)
    have at_x : dist (f a) (f x) ≤ K * (x - a) := hx.1
    rw [dist_comm (f y) (f x), Real.dist_eq, abs_of_pos (sub_pos.mpr xy)] at hy
    calc
      dist (f a) (f y) ≤ dist (f a) (f x) + dist (f x) (f y) := dist_triangle _ _ _
      _ ≤ K * (x - a) + K * (y - x) := add_le_add at_x hy
      _ = K * (y - a) := by ring

open scoped NNReal

/-- A local center bound with finite constant already implies continuity on the domain. -/
theorem continuousOn_of_center_bounds {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (s : Set X) (f : X → Y) (K : ℝ≥0)
    (local_bound : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x) :
    ContinuousOn f s := by
  intro x hx
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε εpos
  have continuous_bound : Continuous (fun y : X => (K : ℝ) * dist y x) :=
    continuous_const.mul (continuous_id.dist continuous_const)
  have limit : Tendsto (fun y : X => (K : ℝ) * dist y x) (𝓝[s] x) (𝓝 0) := by
    have tends : Tendsto (fun y : X => (K : ℝ) * dist y x) (𝓝[s] x)
        (𝓝 ((K : ℝ) * dist x x)) := continuous_bound.continuousWithinAt
    simpa only [dist_self, mul_zero] using tends
  filter_upwards [local_bound x hx, (tendsto_order.mp limit).2 ε εpos] with y hy small
  exact hy.trans_lt small

/-- Near a fixed center, each covering piece that occurs also contains that center. -/
theorem finite_closed_cover_center_bound {X Y ι : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [Finite ι] (s : Set X) (pieces : ι → Set X)
    (closed : ∀ i, IsClosed (pieces i)) (cover : s ⊆ ⋃ i, pieces i)
    (f : X → Y) (K : ℝ≥0) (bounded : ∀ i, LipschitzOnWith K f (pieces i))
    (x : X) :
    ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x := by
  classical
  have exclude (i : ι) : ∀ᶠ y in 𝓝 x, x ∉ pieces i → y ∉ pieces i := by
    by_cases inside : x ∈ pieces i
    · exact Filter.Eventually.of_forall (fun _ h => (h inside).elim)
    · filter_upwards [(closed i).isOpen_compl.mem_nhds inside] with y hy
      exact fun _ => hy
  have all := Filter.eventually_all.mpr exclude
  filter_upwards [all.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy ys
  obtain ⟨i, yi⟩ := Set.mem_iUnion.mp (cover ys)
  have xi : x ∈ pieces i := by
    by_contra outside
    exact hy i outside yi
  exact (bounded i).dist_le_mul y yi x xi

end Unfoldings
