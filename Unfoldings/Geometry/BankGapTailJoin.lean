module

public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.TerminalEdgeRay

/-! Gap tails join their true final bank endpoints with the same final-edge metric speed. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (M : BankGapModel first second)

/-- The infinite bank begins at the literal final closed-edge endpoint on either side. -/
@[simp] theorem tailPoint_zero_eq_edgePoint (side : Bool) :
    M.tailPoint side 0 = M.edgePoint side (Fin.last n) 1 := by
  apply PolygonalPoint.ext
  simp only [tailPoint_val, PolygonalRay.tail_zero, edgePoint_val, PolygonalChain.point_one,
    Fin.succ_last]

variable {P : PolygonalChain ℂ (n + 1)} {events : List (PolygonalChain.Opening (n + 1))}
  (N : BankGapModel P.terminalEdgeRay (P.terminalEdgeRay.openings events))

/-- Continuing the last edge introduces no change of metric parameter at the true rim point.
Both opened banks retain this property, regardless of their accumulated rotations. -/
theorem edist_tailPoint_eq_last_edge (side : Bool) (s t : ℝ≥0) :
    edist (N.tailPoint side s) (N.tailPoint side t) =
      edist (N.edgePoint side (Fin.last n) 0) (N.edgePoint side (Fin.last n) 1) * edist s t := by
  have first : edist (N.tailPoint false s) (N.tailPoint false t) =
      edist (N.edgePoint false (Fin.last n) 0) (N.edgePoint false (Fin.last n) 1) *
        edist s t := by
    rw [N.edist_tailPoint, N.edist_edgePoint]
    have unit : edist (0 : unitInterval) 1 = 1 := by
      rw [edist_dist]
      change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
      norm_num
    rw [unit, mul_one]
    rfl
  cases side
  · exact first
  · exact (N.edist_tailPoint_sides s t).symm.trans
      (first.trans (congrArg (fun d => d * edist s t)
        (N.edist_edgePoint_sides (Fin.last n) 0 1)))

end Unfoldings.BankGapModel
