module

public import Unfoldings.Metric.BallIsometry

/-! Whole patch-ball charts retain their canonical maps under an isometry of the target. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X Y Z : Type*} [EMetricSpace X] [EMetricSpace Y] [EMetricSpace Z]

/-- Move exact patch neighborhoods to an isometric target while preserving the actual inclusion. -/
theorem exists_ball_chart_isometry_target (e : X ≃ᵢ Y) (f : Z → Y) (x : X)
    (chart : ∃ source : Z, f source = e x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (e x) (ENNReal.ofReal r), ∀ z, (B z).val = f z.val) :
    ∃ source : Z, e.symm (f source) = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (B z).val = e.symm (f z.val) := by
  obtain ⟨source, center, r, rpos, B, agrees⟩ := chart
  let move := basedEBallIsometry e.symm (e x) x (e.symm_apply_apply x) (ENNReal.ofReal r)
  refine ⟨source, (congrArg e.symm center).trans (e.symm_apply_apply x), r, rpos, B.trans move, ?_⟩
  intro z
  exact congrArg e.symm (agrees z)

/-- A physical interior condition and its patch charts survive a fold-preserving target isometry. -/
theorem exists_ball_chart_isometry_target_of_fold {S : Type*} (e : X ≃ᵢ Y) (f : Z → Y)
    (left : X → S) (right : Y → S) (inside : S → Prop)
    (agrees : ∀ x, right (e x) = left x)
    (charts : ∀ y, inside (right y) → ∃ source : Z, f source = y ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball y (ENNReal.ofReal r), ∀ z, (B z).val = f z.val)
    (x : X) (positive : inside (left x)) :
    ∃ source : Z, e.symm (f source) = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (B z).val = e.symm (f z.val) :=
  exists_ball_chart_isometry_target e f x
    (charts (e x) (Eq.mpr (congrArg inside (agrees x)) positive))

/-- An inverse target isometry retains the original physical folding identity. -/
theorem map_isometry_symm {S : Type*} (e : X ≃ᵢ Y) (left : X → S) (right : Y → S)
    (agrees : ∀ x, right (e x) = left x) (y : Y) : left (e.symm y) = right y :=
  (agrees (e.symm y)).symm.trans (congrArg right (e.apply_symm_apply y))

end Unfoldings
