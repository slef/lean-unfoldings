module

public import Unfoldings.Metric.OpenChart
public import Unfoldings.Geometry.BallRigidity

/-!
# Constructed rigid transitions between open metric charts

Two charts at the same point restrict to whole balls of one common radius.
Their coordinate transition is an actual isometric ball map. Its proved
rigid extension aligns the charts on a whole ambient neighborhood.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X E F : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]
  {D G : Set X} {U : Set E} {V : Set F}

theorem exists_rigid_chart_transition (left : D ≃ᵢ U) (right : G ≃ᵢ V)
    (open_D : IsOpen D) (open_G : IsOpen G) (open_U : IsOpen U) (open_V : IsOpen V)
    (x : X) (in_D : x ∈ D) (in_G : x ∈ G) :
    ∃ r : ℝ, 0 < r ∧ ∃ inside_D : Metric.ball x r ⊆ D, ∃ inside_G : Metric.ball x r ⊆ G,
      ∃ A : E →ᵃⁱ[ℝ] F, ∀ y : Metric.ball x r,
        A (left ⟨y.val, inside_D y.property⟩).val =
          (right ⟨y.val, inside_G y.property⟩).val := by
  obtain ⟨a, apos, first, left_cover⟩ :=
    exists_open_chart_ball_radius left open_D open_U ⟨x, in_D⟩
  obtain ⟨b, bpos, last, right_cover⟩ :=
    exists_open_chart_ball_radius right open_G open_V ⟨x, in_G⟩
  let r := min a b
  have positive : 0 < r := lt_min apos bpos
  have inside_D : Metric.ball x r ⊆ D :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans first
  have inside_G : Metric.ball x r ⊆ G :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans last
  have cover_U : Metric.ball (left ⟨x, in_D⟩).val r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans left_cover
  have cover_V : Metric.ball (right ⟨x, in_G⟩).val r ⊆ V :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans right_cover
  let L := restrictChartBall left ⟨x, in_D⟩ inside_D cover_U
  let R := restrictChartBall right ⟨x, in_G⟩ inside_G cover_V
  let f := fun z => (R (L.symm z)).val
  have isometry : Isometry f :=
    (isometry_subtype_coe (s := Metric.ball (right ⟨x, in_G⟩).val r)).comp
      (R.isometry.comp L.symm.isometry)
  let B : IsometricBallMap E F :=
    { center := (left ⟨x, in_D⟩).val
      radius := r
      positive := positive
      map := f
      isometry := isometry }
  refine ⟨r, positive, inside_D, inside_G, B.affineExtension, ?_⟩
  intro y
  have equal := B.affineExtension_agrees (L y)
  change B.affineExtension (L y).val = (R (L.symm (L y))).val at equal
  rw [L.symm_apply_apply] at equal
  exact equal

end Unfoldings
