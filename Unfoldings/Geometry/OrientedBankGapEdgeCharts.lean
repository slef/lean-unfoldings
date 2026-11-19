module

public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.TwoBankGapEdgeChart
public import Unfoldings.Geometry.TwoBankGapSecondEdgeChart
public import Unfoldings.Cone.PhysicalSectorChart

/-! The literal canonical gap marks retain their original oriented whole half-plane charts. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {first second : PolygonalRay ℂ n} (G : OrientedBankGap first second)

/-- A named first-bank edge point is its exact original source-radius bank point. -/
theorem model_edgePoint_first (i : Fin n) (t : unitInterval) :
    G.model.edgePoint false i t =
      first.twoBankFirstBankPoint second G.first_outward G.first_nonzero G.second_outward
        G.second_nonzero G.phase G.common ‖first.chain.point i t - first.start‖₊ := by
  apply PolygonalPoint.ext
  exact (first.radialPoint_norm_eq_of_mem G.first_outward G.first_nonzero
    (Or.inl (first.chain.point_mem_path_range i t))).symm

/-- A named second-bank edge point is its exact original source-radius bank point. -/
theorem model_edgePoint_second (i : Fin n) (t : unitInterval) :
    G.model.edgePoint true i t =
      first.twoBankSecondBankPoint second G.first_outward G.first_nonzero G.second_outward
        G.second_nonzero G.phase G.common ‖second.chain.point i t - second.start‖₊ := by
  apply PolygonalPoint.ext
  exact (second.radialPoint_norm_eq_of_mem G.second_outward G.second_nonzero
    (Or.inl (second.chain.point_mem_path_range i t))).symm

/-- Every actual strict first-bank mark has the original occupied left half-plane chart.
The chart retains the literal original point and edge frame. -/
theorem model_first_edge_chart (genuine : ∀ i : Fin n, first.chain.edge i ≠ 0)
    (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : Metric.eball (G.model.edgePoint false i t) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal r),
      ∀ y, first.chain.point i t +
        radialLeftCornerFrame (first.chain.point i t - first.start) (first.chain.edge i)
          ((bisectedSectorFan Real.pi Real.pi_pos
            (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  rw [G.model_edgePoint_first]
  exact first.exists_first_edge_point_chart second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase G.common
    (fun j => Ne.symm (sub_ne_zero.mp (genuine j))) i t bounds

/-- Every actual strict second-bank mark has the original occupied right half-plane chart.
The frame reverses the bank direction, retaining its actual complementary side. -/
theorem model_second_edge_chart (genuine : ∀ i : Fin n, second.chain.edge i ≠ 0)
    (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : Metric.eball (G.model.edgePoint true i t) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal r),
      ∀ y, second.chain.point i t +
        radialRightCornerFrame (second.chain.point i t - second.start) (second.chain.edge i)
          ((bisectedSectorFan Real.pi Real.pi_pos
            (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  rw [G.model_edgePoint_second]
  exact first.exists_second_edge_point_chart second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase G.common
    (fun j => Ne.symm (sub_ne_zero.mp (genuine j))) i t bounds

/-- Keep the actual outgoing first-bank frame or reversed incoming second-bank frame. -/
def edgeFrame (side : Bool) (i : Fin n) (t : unitInterval) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  let R := G.model.bank side
  if side then radialRightCornerFrame (R.chain.point i t - R.start) (R.chain.edge i)
  else radialLeftCornerFrame (R.chain.point i t - R.start) (R.chain.edge i)

/-- Each literal canonical bank mark has a centered whole intrinsic half-plane chart
in its original physical edge frame. Both the occupied side and the center are derived. -/
theorem model_edge_centered_chart
    (genuine : ∀ side i, (G.model.bank side).chain.edge i ≠ 0)
    (side : Bool) (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ (r : ℝ) (positive_radius : 0 < r),
      ∃ A : Metric.eball (G.model.edgePoint side i t) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
          (by linarith [Real.pi_pos])).origin (ENNReal.ofReal r),
        (A ⟨G.model.edgePoint side i t,
          Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_radius)⟩).val =
            (bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])).origin ∧
        ∀ y, (G.model.edgePoint side i t).val + G.edgeFrame side i t
          ((bisectedSectorFan Real.pi Real.pi_pos
            (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  have small : F.totalAngle < 2 * Real.pi := by
    rw [bisectedSectorFan_totalAngle]
    linarith [Real.pi_pos]
  cases side
  · obtain ⟨r, positive, A, physical⟩ := G.model_first_edge_chart (genuine false) i t bounds
    refine ⟨r, positive, A, ?_, physical⟩
    exact F.physical_chart_center small _ positive _ A physical
  · obtain ⟨r, positive, A, physical⟩ := G.model_second_edge_chart (genuine true) i t bounds
    refine ⟨r, positive, A, ?_, physical⟩
    exact F.physical_chart_center small _ positive _ A physical

end Unfoldings.OrientedBankGap
