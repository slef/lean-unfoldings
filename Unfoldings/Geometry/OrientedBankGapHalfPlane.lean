module

public import Unfoldings.Geometry.OrientedBankGapEdgeParameters
public import Unfoldings.Cone.HalfTurnMetric
public import Unfoldings.Metric.BankHalfPlaneFrames
public import Unfoldings.Metric.BallIsometry

/-! Normalize an actual canonical gap bank chart to forward original arclength. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.OrientedBankGap

open MetricGluing

variable {n : ℕ} {first second : PolygonalRay ℂ n} (G : OrientedBankGap first second)

/-- Either occupied half-plane can represent the original gap bank. The real axis keeps
the same original parameter and speed even on the reversed second bank. -/
theorem exists_model_edge_normalized_chart
    (genuine : ∀ side i, (G.model.bank side).chain.edge i ≠ 0)
    (bank_side occupied : Bool) (i : Fin n) (t : unitInterval) (bounds : 0 < t ∧ t < 1) :
    ∃ r, Nonempty (BankHalfPlaneChart (G.model.edgePoint bank_side i) t occupied
      (fun s : unitInterval => (s.val - t.val) * ‖(G.model.bank bank_side).chain.edge i‖) r) := by
  let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  obtain ⟨r, positive, A, center, physical⟩ :=
    G.model_edge_centered_chart genuine bank_side i t bounds
  let B := halfTurnFanIsometry.trans (bankUpperNormalize bank_side occupied)
  have model_center : B F.origin = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change bankAxisFrame bank_side occupied (halfTurnFanIsometry F.origin).val = 0
    rw [halfTurnFanIsometry_val, F.develop_origin, map_zero]
  let C := basedEBallIsometry B F.origin (bankHalfPlaneOrigin occupied) model_center
    (ENNReal.ofReal r)
  refine ⟨r, ⟨⟨positive, A.trans C, ?_, ?_⟩⟩⟩
  · change B (A ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = _
    exact (congrArg B center).trans model_center
  · intro s near
    change bankAxisFrame bank_side occupied
      (halfTurnFanIsometry (A ⟨_, near⟩).val).val = _
    rw [halfTurnFanIsometry_val]
    cases bank_side
    · rw [G.model_first_edge_chart_parameter (genuine false) i t bounds.1 F A physical s near,
        bankAxisFrame_ofReal]
      rfl
    · rw [G.model_second_edge_chart_parameter (genuine true) i t bounds.1 F A physical s near,
        bankAxisFrame_ofReal]
      change ((-((t.val - s.val) * ‖second.chain.edge i‖) : ℝ) : ℂ) =
        (((s.val - t.val) * ‖second.chain.edge i‖ : ℝ) : ℂ)
      exact congrArg Complex.ofReal (by ring)

end Unfoldings.OrientedBankGap
