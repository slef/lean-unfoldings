module

public import Unfoldings.Geometry.OrientedBankGapEdgeCharts
public import Unfoldings.Geometry.RadialCornerFrameParameters

/-! Physical gap edge charts preserve original bank parameters with their actual orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.OrientedBankGap

variable {n m : ℕ} {first second : PolygonalRay ℂ n} (G : OrientedBankGap first second)

/-- In a physical first-bank chart, original forward displacement is positive real arclength.
The chart need not be normalized independently; its original physical formula determines it. -/
theorem model_first_edge_chart_parameter (genuine : ∀ i : Fin n, first.chain.edge i ≠ 0)
    (i : Fin n) (t : unitInterval) (positive_time : 0 < t) {r : ℝ} (F : AngularFan m)
    (A : Metric.eball (G.model.edgePoint false i t) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball F.origin (ENNReal.ofReal r))
    (physical : ∀ y, first.chain.point i t +
      radialLeftCornerFrame (first.chain.point i t - first.start) (first.chain.edge i)
        (F.develop (A y).val) = y.val.val)
    (s : unitInterval)
    (near : G.model.edgePoint false i s ∈ Metric.eball (G.model.edgePoint false i t)
      (ENNReal.ofReal r)) :
    F.develop (A ⟨G.model.edgePoint false i s, near⟩).val =
      (((s : ℝ) - (t : ℝ)) * ‖first.chain.edge i‖ : ℝ) := by
  have vertices : ∀ j : Fin n, first.chain.vertex j.castSucc ≠ first.chain.vertex j.succ :=
    fun j => Ne.symm (sub_ne_zero.mp (genuine j))
  have radial_ne : first.chain.point i t - first.start ≠ 0 :=
    sub_ne_zero.mpr (first.point_ne_start G.first_outward vertices i t positive_time)
  apply (radialLeftCornerFrame (first.chain.point i t - first.start)
    (first.chain.edge i)).injective
  apply add_left_cancel (a := first.chain.point i t)
  have expected : first.chain.point i t +
      radialLeftCornerFrame (first.chain.point i t - first.start) (first.chain.edge i)
        ((((s : ℝ) - (t : ℝ)) * ‖first.chain.edge i‖ : ℝ) : ℂ) = first.chain.point i s := by
    rw [radialLeftCornerFrame_real_length _ _ radial_ne (genuine i)]
    simp only [PolygonalChain.point, AffineMap.lineMap_apply_module', PolygonalChain.edge]
    module
  exact (physical ⟨G.model.edgePoint false i s, near⟩).trans expected.symm

/-- The occupied second-bank frame reverses the same original parameter, so increasing
bank time gives negative real displacement. Both sides keep the same original speed. -/
theorem model_second_edge_chart_parameter (genuine : ∀ i : Fin n, second.chain.edge i ≠ 0)
    (i : Fin n) (t : unitInterval) (positive_time : 0 < t) {r : ℝ} (F : AngularFan m)
    (A : Metric.eball (G.model.edgePoint true i t) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball F.origin (ENNReal.ofReal r))
    (physical : ∀ y, second.chain.point i t +
      radialRightCornerFrame (second.chain.point i t - second.start) (second.chain.edge i)
        (F.develop (A y).val) = y.val.val)
    (s : unitInterval)
    (near : G.model.edgePoint true i s ∈ Metric.eball (G.model.edgePoint true i t)
      (ENNReal.ofReal r)) :
    F.develop (A ⟨G.model.edgePoint true i s, near⟩).val =
      (((t : ℝ) - (s : ℝ)) * ‖second.chain.edge i‖ : ℝ) := by
  have vertices : ∀ j : Fin n, second.chain.vertex j.castSucc ≠ second.chain.vertex j.succ :=
    fun j => Ne.symm (sub_ne_zero.mp (genuine j))
  have radial_ne : second.chain.point i t - second.start ≠ 0 :=
    sub_ne_zero.mpr (second.point_ne_start G.second_outward vertices i t positive_time)
  apply (radialRightCornerFrame (second.chain.point i t - second.start)
    (second.chain.edge i)).injective
  apply add_left_cancel (a := second.chain.point i t)
  have expected : second.chain.point i t +
      radialRightCornerFrame (second.chain.point i t - second.start) (second.chain.edge i)
        ((((t : ℝ) - (s : ℝ)) * ‖second.chain.edge i‖ : ℝ) : ℂ) = second.chain.point i s := by
    rw [radialRightCornerFrame_real_length _ _ radial_ne (genuine i)]
    simp only [PolygonalChain.point, AffineMap.lineMap_apply_module', PolygonalChain.edge]
    module
  exact (physical ⟨G.model.edgePoint true i s, near⟩).trans expected.symm

end Unfoldings.OrientedBankGap
