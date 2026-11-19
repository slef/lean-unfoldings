module

public import Unfoldings.Geometry.OrientedBankGapHalfPlane
public import Unfoldings.Geometry.TwoBankGapTailInteriorChart
public import Unfoldings.Geometry.TwoBankGapSecondTailInteriorChart

/-! The actual canonical whole tails have normalized forward arclength charts. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.OrientedBankGap

open MetricGluing

variable {n : ℕ} {first second : PolygonalRay ℂ n} (G : OrientedBankGap first second)

private theorem model_tailPoint_first (t : ℝ≥0) :
    G.model.tailPoint false t =
      first.twoBankFirstBankPoint second G.first_outward G.first_nonzero G.second_outward
        G.second_nonzero G.phase G.common ‖first.tail t - first.start‖₊ := by
  apply PolygonalPoint.ext
  exact (first.radialPoint_norm_eq_of_mem G.first_outward G.first_nonzero
    (Or.inr ⟨t, rfl⟩)).symm

private theorem model_tailPoint_second (t : ℝ≥0) :
    G.model.tailPoint true t =
      first.twoBankSecondBankPoint second G.first_outward G.first_nonzero G.second_outward
        G.second_nonzero G.phase G.common ‖second.tail t - second.start‖₊ := by
  apply PolygonalPoint.ext
  exact (second.radialPoint_norm_eq_of_mem G.second_outward G.second_nonzero
    (Or.inr ⟨t, rfl⟩)).symm

/-- An ordinary positive tail point has normalized forward arclength in either half-plane. -/
theorem exists_model_tail_normalized_chart (side occupied : Bool) (t : ℝ≥0)
    (positive_time : 0 < t) :
    ∃ r, Nonempty (BankHalfPlaneChart (G.model.tailPoint side) t occupied
      (fun s : ℝ≥0 => (s.val - t.val) * ‖(G.model.bank side).direction‖) r) := by
  let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  let R := G.model.bank side
  let p := R.tail t
  let frame := if side then radialRightCornerFrame (p - R.start) R.direction
    else radialLeftCornerFrame (p - R.start) R.direction
  have physical_chart : ∃ (r : ℝ), 0 < r ∧ ∃ A :
      Metric.eball (G.model.tailPoint side t) (ENNReal.ofReal r) ≃ᵢ
        Metric.eball F.origin (ENNReal.ofReal r),
      ∀ y, p + frame (F.develop (A y).val) = y.val.val := by
    cases side
    · rw [G.model_tailPoint_first]
      exact first.exists_first_tail_point_chart second G.first_outward G.first_nonzero
        G.second_outward G.second_nonzero G.phase G.common t positive_time
    · rw [G.model_tailPoint_second]
      exact first.exists_second_tail_point_chart second G.first_outward G.first_nonzero
        G.second_outward G.second_nonzero G.phase G.common t positive_time
  obtain ⟨r, rpos, A, physical⟩ := physical_chart
  have radial : 0 < inner ℝ (p - R.start) R.direction := by
    cases side
    · exact first.inner_tail_point_pos G.first_outward G.first_nonzero t positive_time
    · exact second.inner_tail_point_pos G.second_outward G.second_nonzero t positive_time
  have radial_ne : p - R.start ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at radial
    exact (lt_irrefl _ radial)
  have angle : F.totalAngle < 2 * Real.pi := by
    rw [bisectedSectorFan_totalAngle]
    linarith [Real.pi_pos]
  have center := F.physical_chart_center angle (G.model.tailPoint side t) rpos frame A physical
  let B := halfTurnFanIsometry.trans (bankUpperNormalize side occupied)
  have model_center : B F.origin = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change bankAxisFrame side occupied (halfTurnFanIsometry F.origin).val = 0
    rw [halfTurnFanIsometry_val, F.develop_origin, map_zero]
  refine ⟨r, ⟨⟨rpos, A.trans (basedEBallIsometry B _ _ model_center (ENNReal.ofReal r)),
    ?_, ?_⟩⟩⟩
  · exact (congrArg B center).trans model_center
  · intro s near
    let u := if side then t.val - s.val else s.val - t.val
    have coordinate : F.develop (A ⟨_, near⟩).val = ((u * ‖R.direction‖ : ℝ) : ℂ) := by
      apply frame.injective
      apply add_left_cancel (a := p)
      refine (physical ⟨_, near⟩).trans ?_
      change R.tail s = p + frame _
      cases side
      · change first.tail s = first.tail t + radialLeftCornerFrame
          (first.tail t - first.start) first.direction
          (((s.val - t.val) * ‖first.direction‖ : ℝ) : ℂ)
        rw [radialLeftCornerFrame_real_length _ _ (show first.tail t - first.start ≠ 0 from
          radial_ne) G.first_nonzero (s.val - t.val)]
        change first.chain.vertex (Fin.last n) + s.val • first.direction =
          (first.chain.vertex (Fin.last n) + t.val • first.direction) +
            (s.val - t.val) • first.direction
        module
      · change second.tail s = second.tail t + radialRightCornerFrame
          (second.tail t - second.start) second.direction
          (((t.val - s.val) * ‖second.direction‖ : ℝ) : ℂ)
        rw [radialRightCornerFrame_real_length _ _ (show second.tail t - second.start ≠ 0 from
          radial_ne) G.second_nonzero (t.val - s.val)]
        change second.chain.vertex (Fin.last n) + s.val • second.direction =
          (second.chain.vertex (Fin.last n) + t.val • second.direction) +
            (t.val - s.val) • (-second.direction)
        module
    change bankAxisFrame side occupied (halfTurnFanIsometry (A ⟨_, near⟩).val).val = _
    rw [halfTurnFanIsometry_val, coordinate, bankAxisFrame_ofReal]
    cases side
    · rfl
    · apply congrArg Complex.ofReal
      change -((t.val - s.val) * ‖R.direction‖) = (s.val - t.val) * ‖R.direction‖
      ring

end Unfoldings.OrientedBankGap
