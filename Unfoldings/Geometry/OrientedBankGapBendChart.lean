module

public import Unfoldings.Cone.PhysicalSectorChart
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.TwoBankGapInternalCorner
public import Unfoldings.Geometry.TwoBankGapSecondInternalCorner

/-! Intrinsic sector charts at the original finite marks of a canonical gap. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : OrientedBankGap first second)

/-- The actual closed-edge mark at a bend has a centered sector ball with the occupied
aperture and physical frame of its two incident edges. -/
theorem exists_model_bend_chart (side : Bool) (k : Fin n)
    (genuine : ∀ i, (G.model.bank side).chain.edge i ≠ 0)
    (radial : 0 < inner ℝ ((G.model.bank side).chain.vertex k.succ.castSucc -
      (G.model.bank side).start) ((G.model.bank side).chain.edge k.succ)) :
    let R := G.model.bank side
    let p := R.chain.vertex k.succ.castSucc
    let incoming := R.chain.edge k.castSucc
    let outgoing := R.chain.edge k.succ
    let width := if side then radialRightCornerWidth (p - R.start) incoming outgoing
      else radialLeftCornerWidth (p - R.start) incoming outgoing
    let frame := if side then radialRightCornerFrame (p - R.start) incoming
      else radialLeftCornerFrame (p - R.start) outgoing
    ∃ (pos : 0 < width) (small : width < 2 * Real.pi) (r : ℝ) (positive : 0 < r),
      let F := bisectedSectorFan width pos small
      let x := G.model.edgePoint side k.succ 0
      ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ Metric.eball F.origin (ENNReal.ofReal r),
        (A ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = F.origin ∧
        ∀ y, p + frame (F.develop (A y).val) = y.val.val := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
    let R := G.model.bank side
    let p := R.chain.vertex k.succ.castSucc
    let incoming := R.chain.edge k.castSucc
    let outgoing := R.chain.edge k.succ
    let width := if side then radialRightCornerWidth (p - R.start) incoming outgoing
      else radialLeftCornerWidth (p - R.start) incoming outgoing
    let frame := if side then radialRightCornerFrame (p - R.start) incoming
      else radialLeftCornerFrame (p - R.start) outgoing
    let x := G.model.edgePoint side k.succ 0
    have base : x.val = p := (R.chain.point_zero k.succ)
    have clear (i : Fin (n + 2)) : R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ :=
      fun eq => genuine i (sub_eq_zero.mpr eq.symm)
    have physical : ∃ (pos : 0 < width) (small : width < 2 * Real.pi) (r : ℝ),
        0 < r ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (bisectedSectorFan width pos small).origin (ENNReal.ofReal r),
          ∀ y, p + frame ((bisectedSectorFan width pos small).develop (A y).val) = y.val.val := by
      cases side
      · have center : x = first.twoBankFirstVertexPoint second G.first_outward G.first_nonzero
            G.second_outward G.second_nonzero G.phase G.common k.succ.castSucc := by
          apply PolygonalPoint.ext
          exact base.trans (first.twoBankFirstVertexPoint_val second G.first_outward G.first_nonzero
            G.second_outward G.second_nonzero G.phase G.common k.succ.castSucc).symm
        rw [center]
        obtain ⟨pos, small, _, chart⟩ := first.exists_first_internal_vertex_chart second
          G.first_outward G.first_nonzero G.second_outward G.second_nonzero G.phase G.common
          clear k radial
        exact ⟨pos, small, chart⟩
      · have center : x = first.twoBankSecondVertexPoint second G.first_outward G.first_nonzero
            G.second_outward G.second_nonzero G.phase G.common k.succ.castSucc := by
          apply PolygonalPoint.ext
          exact base.trans (first.twoBankSecondVertexPoint_val second G.first_outward
            G.first_nonzero G.second_outward G.second_nonzero G.phase G.common k.succ.castSucc).symm
        rw [center]
        obtain ⟨pos, small, _, chart⟩ := first.exists_second_internal_vertex_chart second
          G.first_outward G.first_nonzero G.second_outward G.second_nonzero G.phase G.common
          clear k radial
        exact ⟨pos, small, chart⟩
    obtain ⟨pos, small, r, positive, A, chart⟩ := physical
    refine ⟨pos, small, r, positive, A, ?_, chart⟩
    let F := bisectedSectorFan width pos small
    have angle : F.totalAngle < 2 * Real.pi := by
      rw [bisectedSectorFan_totalAngle]
      exact small
    exact F.physical_chart_center angle x positive frame A
      (fun y => (congrArg (fun z => z + frame (F.develop (A y).val)) base).trans (chart y))

end Unfoldings.OrientedBankGap
