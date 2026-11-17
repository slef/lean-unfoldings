module

public import Unfoldings.Geometry.SpatialEnvelopeCutExcision

/-! Local cut equality gives whole-ball charts at arbitrary actual metric copies. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- A local equality of actual cut carriers preserves a whole intrinsic ball at every
original metric copy, retaining the canonical restoration map and all endpoint classes. -/
theorem exists_forgetCut_ball_chart_at (cuts other : Set Plane) (included : other ⊆ cuts)
    (x : P.Cut cuts) {ε : ℝ} (positive : 0 < ε)
    (same : ∀ z, dist z (Cap.horizontal (P.restoreCut cuts x).val) < ε →
      (z ∈ cuts ↔ z ∈ other)) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (P.forgetCut cuts other included x) (ENNReal.ofReal r),
      ∀ y, (B y).val = P.forgetCut cuts other included y.val := by
  obtain ⟨a, represents⟩ := MetricGluing.point_surjective (fun a => P.planarCell a)
    (P.cutGlue cuts) x
  obtain ⟨chart⟩ := P.exists_forgetCut_ball_chart cuts other included a positive (by
    intro z near
    apply same z
    rwa [← represents])
  have result : ∃ r : ℝ, 0 < r ∧ ∃ B :
      Metric.eball (MetricGluing.point (fun a => P.planarCell a) (P.cutGlue cuts) a)
        (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (P.forgetCut cuts other included
        (MetricGluing.point (fun a => P.planarCell a) (P.cutGlue cuts) a)) (ENNReal.ofReal r),
      ∀ y, (B y).val = P.forgetCut cuts other included y.val :=
    ⟨chart.radius, chart.positive, chart.chart, chart.agrees⟩
  rwa [represents] at result

end Unfoldings.SpatialEnvelope.WholePartition
