module

public import Unfoldings.Geometry.OrientedBankGapTailHalfPlane
public import Unfoldings.Geometry.TwoBankGapTailCorner
public import Unfoldings.Geometry.TwoBankGapSecondTailCorner

/-! An original terminal joint on a straight bank has the actual occupied half-plane. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.OrientedBankGap

private theorem exists_halfTurnPhysicalChart {S : Set ℂ} (x : PolygonalPoint S)
    (p : ℂ) (frame : ℂ ≃ₗᵢ[ℝ] ℂ) {width : ℝ} (angle : width = Real.pi)
    (pos : 0 < width) (small : width < 2 * Real.pi)
    (chart : ∃ r : ℝ, 0 < r ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (bisectedSectorFan width pos small).origin (ENNReal.ofReal r),
      ∀ y, p + frame ((bisectedSectorFan width pos small).develop (A y).val) = y.val.val) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).origin (ENNReal.ofReal r),
      ∀ y, p + frame ((bisectedSectorFan Real.pi Real.pi_pos
        (by linarith [Real.pi_pos])).develop (A y).val) = y.val.val := by
  subst width
  exact chart

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : OrientedBankGap first second)

/-- The straight join keeps the physical corner frame of the whole gap and its actual center. -/
theorem exists_model_straightJoin_chart
    (side : Bool) (straight : (G.model.bank side).direction =
      (G.model.bank side).chain.edge (Fin.last n))
    (genuine : ∀ i, (G.model.bank side).chain.edge i ≠ 0) :
    let R := G.model.bank side
    let p := R.chain.vertex (Fin.last (n + 1))
    let frame := if side then radialRightCornerFrame (p - R.start) R.direction
      else radialLeftCornerFrame (p - R.start) R.direction
    let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
    ∃ (r : ℝ) (positive : 0 < r), ∃ A :
      Metric.eball (G.model.tailPoint side 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball F.origin (ENNReal.ofReal r),
      (A ⟨G.model.tailPoint side 0,
        Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = F.origin ∧
      ∀ y, p + frame (F.develop (A y).val) = y.val.val := by
  let R := G.model.bank side
  let p := R.chain.vertex (Fin.last (n + 1))
  let frame := if side then radialRightCornerFrame (p - R.start) R.direction
    else radialLeftCornerFrame (p - R.start) R.direction
  let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  have clear (i : Fin (n + 1)) : R.chain.vertex i.castSucc ≠ R.chain.vertex i.succ :=
    fun eq => genuine i (sub_eq_zero.mpr eq.symm)
  have outward : R.Outward := by
    cases side
    · exact G.first_outward
    · exact G.second_outward
  have radial : 0 < inner ℝ (p - R.start) R.direction := by
    rw [straight]
    exact R.inner_terminal_edge_pos outward (Fin.last n) (clear _)
  have base : (G.model.tailPoint side 0).val = p := by
    change R.tail 0 = p
    simp [PolygonalRay.tail, p]
  have physical : ∃ r : ℝ, 0 < r ∧ ∃ A :
      Metric.eball (G.model.tailPoint side 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball F.origin (ENNReal.ofReal r),
      ∀ y, p + frame (F.develop (A y).val) = y.val.val := by
    cases side
    · have named : G.model.tailPoint false 0 =
          first.twoBankFirstBankPoint second G.first_outward G.first_nonzero G.second_outward
            G.second_nonzero G.phase G.common ‖p - first.start‖₊ := by
        apply PolygonalPoint.ext
        exact base.trans (first.radialPoint_vertex G.first_outward G.first_nonzero
          (Fin.last (n + 1))).symm
      have width : radialLeftCornerWidth (p - first.start)
          (p - first.chain.vertex (Fin.last n).castSucc) first.direction = Real.pi := by
        have edge : p - first.chain.vertex (Fin.last n).castSucc = first.direction := straight.symm
        rw [edge]
        simp only [radialLeftCornerWidth, add_sub_cancel_right]
      rw [named]
      obtain ⟨pos, small, _, chart⟩ := first.exists_first_terminal_vertex_chart second
        G.first_outward G.first_nonzero G.second_outward G.second_nonzero G.phase G.common
        clear radial
      exact exists_halfTurnPhysicalChart _ p _ width pos small chart
    · have named : G.model.tailPoint true 0 =
          first.twoBankSecondBankPoint second G.first_outward G.first_nonzero G.second_outward
            G.second_nonzero G.phase G.common ‖p - second.start‖₊ := by
        apply PolygonalPoint.ext
        exact base.trans (second.radialPoint_vertex G.second_outward G.second_nonzero
          (Fin.last (n + 1))).symm
      have edge : p - second.chain.vertex (Fin.last n).castSucc = second.direction :=
        straight.symm
      have width : radialRightCornerWidth (p - second.start)
          (p - second.chain.vertex (Fin.last n).castSucc) second.direction = Real.pi := by
        rw [edge]
        simp only [radialRightCornerWidth, radialLeftCornerWidth, add_sub_cancel_right]
      rw [named]
      obtain ⟨pos, small, _, chart⟩ := first.exists_second_terminal_vertex_chart second
        G.first_outward G.first_nonzero G.second_outward G.second_nonzero G.phase G.common
        clear radial
      have matching : radialRightCornerFrame (p - second.start)
          (p - second.chain.vertex (Fin.last n).castSucc) = frame := by
        change radialRightCornerFrame (p - second.start)
          (p - second.chain.vertex (Fin.last n).castSucc) =
            radialRightCornerFrame (p - second.start) second.direction
        rw [edge]
      rw [← matching]
      exact exists_halfTurnPhysicalChart _ p _ width pos small chart
  obtain ⟨r, positive, A, physical_A⟩ := physical
  refine ⟨r, positive, A, ?_, physical_A⟩
  have half : F.totalAngle < 2 * Real.pi := by
    rw [bisectedSectorFan_totalAngle]
    linarith [Real.pi_pos]
  exact F.physical_chart_center half (G.model.tailPoint side 0) positive frame A
    (fun y => (congrArg (fun z => z + frame (F.develop (A y).val)) base).trans (physical_A y))

end Unfoldings.OrientedBankGap
