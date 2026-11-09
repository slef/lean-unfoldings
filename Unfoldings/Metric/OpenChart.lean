module

public import Mathlib.Topology.MetricSpace.Isometry

/-! Recenter an open isometric chart on a whole ambient metric ball. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X E : Type*} [MetricSpace X] [MetricSpace E]
  {D : Set X} {U : Set E}

def restrictChartBall (chart : D ≃ᵢ U) (x : D) {r : ℝ}
    (inside : Metric.ball x.val r ⊆ D)
    (cover : Metric.ball (chart x).val r ⊆ U) :
    Metric.ball x.val r ≃ᵢ Metric.ball (chart x).val r where
  toFun y := ⟨(chart ⟨y.val, inside y.property⟩).val, by
    change dist (chart ⟨y.val, inside y.property⟩) (chart x) < r
    rw [chart.isometry.dist_eq]
    exact y.property⟩
  invFun y := ⟨(chart.symm ⟨y.val, cover y.property⟩).val, by
    change dist (chart.symm ⟨y.val, cover y.property⟩) x < r
    rw [← chart.isometry.dist_eq, chart.apply_symm_apply]
    exact y.property⟩
  left_inv y := by
    apply Subtype.ext
    change (chart.symm (chart ⟨y.val, inside y.property⟩)).val = y.val
    exact congrArg Subtype.val (chart.symm_apply_apply ⟨y.val, inside y.property⟩)
  right_inv y := by
    apply Subtype.ext
    change (chart (chart.symm ⟨y.val, cover y.property⟩)).val = y.val
    exact congrArg Subtype.val (chart.apply_symm_apply ⟨y.val, cover y.property⟩)
  isometry_toFun y z := chart.isometry ⟨y.val, inside y.property⟩ ⟨z.val, inside z.property⟩

@[simp] theorem restrictChartBall_apply (chart : D ≃ᵢ U) (x : D) {r : ℝ}
    (inside : Metric.ball x.val r ⊆ D) (cover : Metric.ball (chart x).val r ⊆ U)
    (y : Metric.ball x.val r) :
    (restrictChartBall chart x inside cover y).val = (chart ⟨y.val, inside y.property⟩).val := rfl

theorem exists_open_chart_ball_radius (chart : D ≃ᵢ U) (open_D : IsOpen D) (open_U : IsOpen U)
    (x : D) : ∃ r : ℝ, 0 < r ∧ Metric.ball x.val r ⊆ D ∧ Metric.ball (chart x).val r ⊆ U := by
  obtain ⟨a, apos, first⟩ := Metric.isOpen_iff.mp open_D x.val x.property
  obtain ⟨b, bpos, last⟩ := Metric.isOpen_iff.mp open_U (chart x).val (chart x).property
  exact ⟨min a b, lt_min apos bpos,
    (Metric.ball_subset_ball (min_le_left _ _)).trans first,
    (Metric.ball_subset_ball (min_le_right _ _)).trans last⟩

end Unfoldings
