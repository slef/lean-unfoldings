module

public import Unfoldings.Metric.EuclideanAtlas

/-! Euclidean metric atlases on open regions of an ambient metric space. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X] (U : Set X) (open_U : IsOpen U)

/-- Restrict a whole ambient ball to an open subspace that contains it. -/
def openSubspaceBall (x : U) (r : ℝ) (inside : Metric.ball x.val r ⊆ U) :
    Metric.ball x r ≃ᵢ Metric.ball x.val r where
  toEquiv :=
    { toFun y := ⟨y.val.val, y.property⟩
      invFun y := ⟨⟨y.val, inside y.property⟩, y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  isometry_toFun _ _ := rfl

include open_U in
theorem exists_openSubspace_chart (x : U) (regular : HasMetricBallChart Plane x.val) :
    Nonempty (EuclideanChartAt U x) := by
  obtain ⟨D, V, open_D, member, open_V, ⟨chart⟩⟩ := regular.exists_open_chart
  obtain ⟨a, apos, first, cover⟩ :=
    exists_open_chart_ball_radius chart open_D open_V ⟨x.val, member⟩
  obtain ⟨b, bpos, last⟩ := Metric.isOpen_iff.mp open_U x.val x.property
  let radius := min a b
  have positive : 0 < radius := lt_min apos bpos
  have in_D : Metric.ball x.val radius ⊆ D :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans first
  have in_U : Metric.ball x.val radius ⊆ U :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans last
  have covered : Metric.ball (chart ⟨x.val, member⟩).val radius ⊆ V :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans cover
  exact ⟨{ domain := Metric.ball x radius
           image := Metric.ball (chart ⟨x.val, member⟩).val radius
           chart := (openSubspaceBall U x radius in_U).trans
             (restrictChartBall chart ⟨x.val, member⟩ in_D covered)
           open_domain := Metric.isOpen_ball
           open_image := Metric.isOpen_ball
           center_mem := Metric.mem_ball_self positive }⟩

def EuclideanAtlas.onOpen (regular : ∀ x ∈ U, HasMetricBallChart Plane x) : EuclideanAtlas U :=
  fun x => Classical.choice (exists_openSubspace_chart U open_U x (regular x.val x.property))

end Unfoldings
