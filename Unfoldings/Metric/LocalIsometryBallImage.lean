module

public import Unfoldings.Basic
public import Unfoldings.Metric.RegularLocus
public import Unfoldings.Geometry.ConvexRigidity
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! Local isometries at genuine Euclidean regular points map sufficiently small balls onto balls. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X] {x : X}

theorem HasMetricBallChart.local_isometry_ball_image (regular : HasMetricBallChart Plane x)
    (f : X → Plane) (local_isometry : ∃ r > 0, Isometry (fun y : Metric.ball x r => f y.val))
    {V : Set X} (opened : IsOpen V) (inside : x ∈ V) :
    ∃ r > 0, Metric.ball x r ⊆ V ∧ f '' Metric.ball x r = Metric.ball (f x) r := by
  obtain ⟨D, U, open_D, in_D, open_U, ⟨chart⟩⟩ := regular.exists_open_chart
  let origin : D := ⟨x, in_D⟩
  obtain ⟨a, apos, domain, range⟩ := exists_open_chart_ball_radius chart open_D open_U origin
  obtain ⟨b, bpos, isometry⟩ := local_isometry
  obtain ⟨c, cpos, in_V⟩ := Metric.isOpen_iff.mp opened x inside
  let r := min a (min b c)
  have positive : 0 < r := lt_min apos (lt_min bpos cpos)
  have small_a : r ≤ a := min_le_left _ _
  have small_b : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have small_c : r ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have domain' : Metric.ball x r ⊆ D := (Metric.ball_subset_ball small_a).trans domain
  have range' : Metric.ball (chart origin).val r ⊆ U :=
    (Metric.ball_subset_ball small_a).trans range
  let H := restrictChartBall chart origin domain' range'
  let z := (chart origin).val
  let G (p : Metric.ball z r) := f (H.symm p).val
  have G_isometry : Isometry G := by
    intro p q
    let first : Metric.ball x b :=
      ⟨(H.symm p).val, (Metric.ball_subset_ball small_b) (H.symm p).property⟩
    let last : Metric.ball x b :=
      ⟨(H.symm q).val, (Metric.ball_subset_ball small_b) (H.symm q).property⟩
    exact (isometry first last).trans (H.symm.isometry p q)
  have full : (interior (Metric.ball z r)).Nonempty := by
    rw [Metric.isOpen_ball.interior_eq]
    exact ⟨z, Metric.mem_ball_self positive⟩
  obtain ⟨A, agrees⟩ := exists_rigid_extension_convex (convex_ball z r) full G G_isometry
  let center : Metric.ball x r := ⟨x, Metric.mem_ball_self positive⟩
  have center_value : (H center).val = z := rfl
  have at_center : A z = f x := by
    have equal := agrees (H center)
    change A (H center).val = f (H.symm (H center)).val at equal
    rw [H.symm_apply_apply, center_value] at equal
    exact equal
  have images : f '' Metric.ball x r = A '' Metric.ball z r := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, member, rfl⟩
      let p : Metric.ball x r := ⟨y, member⟩
      refine ⟨(H p).val, (H p).property, ?_⟩
      have equal := agrees (H p)
      change A (H p).val = f (H.symm (H p)).val at equal
      simpa only [H.symm_apply_apply] using equal
    · rintro _ ⟨y, member, rfl⟩
      let p : Metric.ball z r := ⟨y, member⟩
      exact ⟨(H.symm p).val, (H.symm p).property, (agrees p).symm⟩
  refine ⟨r, positive, (Metric.ball_subset_ball small_c).trans in_V, ?_⟩
  rw [images]
  change A.toIsometryEquiv '' Metric.ball z r = Metric.ball (f x) r
  rw [A.toIsometryEquiv.image_ball]
  exact congrArg (fun p => Metric.ball p r) at_center

end Unfoldings
