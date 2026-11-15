module

public import Unfoldings.Cone.IntervalIsometry
public import Unfoldings.Cone.AngularClosure
public import Unfoldings.Metric.Reparametrize

/-! Closing just the two original banks of an actual full-turn retained tangent fan. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (w : C.Vertex retain) {n : ℕ}
  (c : (C.linkSystem retain w).Chain n) (covers : ∀ p, c.Visited p)
  (start : C.linkMate retain w c.first = c.first)
  (finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last)

/-- Preserve the retained tangent fan metric in its original ordered angular coordinates. -/
def intervalClosureCoordinates (_ : Unit) : C.TangentFan retain w ≃ᵢ
    (C.linkAngularFan retain w c).Surface :=
  (C.intervalFanIsometry retain w c covers start finish).symm

/-- Only the two original outer banks are restored, at their equal actual radii. -/
def intervalBankClosingRelation :=
  MetricGluing.reparametrizeGlue (C.intervalClosureCoordinates retain w c covers start finish)
    (C.linkAngularFan retain w c).closingRelation

abbrev ClosedIntervalTangentFan :=
  MetricGluing.Realization (fun _ : Unit => C.TangentFan retain w)
    (C.intervalBankClosingRelation retain w c covers start finish)

def closeIntervalTangentFan (x : C.TangentFan retain w) :
    C.ClosedIntervalTangentFan retain w c covers start finish :=
  MetricGluing.of (fun _ : Unit => C.TangentFan retain w)
    (C.intervalBankClosingRelation retain w c covers start finish) () x

/-- The two actual ordered banks are identified without adding a positive sector. -/
theorem closeIntervalTangentFan_outer_banks (r : ℝ≥0) :
    let A := C.linkAngularFan retain w c
    C.closeIntervalTangentFan retain w c covers start finish
      (C.intervalFanIsometry retain w c covers start finish
        (A.faceMap (Fin.last n) (A.finish (Fin.last n) r))) =
    C.closeIntervalTangentFan retain w c covers start finish
      (C.intervalFanIsometry retain w c covers start finish (A.faceMap 0 (A.start 0 r))) := by
  apply MetricGluing.point_eq_of_glue
  refine ⟨r, ?_, ?_⟩
  all_goals
    change (C.intervalFanIsometry retain w c covers start finish).symm
      ((C.intervalFanIsometry retain w c covers start finish) _) = _
    exact IsometryEquiv.symm_apply_apply _ _

/-- A full-turn retained tangent fan becomes the exact plane metric on closing its banks. -/
def intervalBankClosurePlaneIsometryEquiv (full : C.totalAngle retain w = 2 * Real.pi) :
    C.ClosedIntervalTangentFan retain w c covers start finish ≃ᵢ ℂ :=
  (MetricGluing.reparametrizeIsometryEquiv
    (C.intervalClosureCoordinates retain w c covers start finish)
    (C.linkAngularFan retain w c).closingRelation).trans
      ((C.linkAngularFan retain w c).closedPlaneIsometryEquiv
        (by rwa [C.linkAngularFan_totalAngle retain w c covers]))

/-- Original corner placements are unchanged by the zero-defect bank closure. -/
@[simp] theorem intervalBankClosurePlane_angularToTangent
    (full : C.totalAngle retain w = 2 * Real.pi) (x : (C.linkAngularFan retain w c).Surface) :
    C.intervalBankClosurePlaneIsometryEquiv retain w c covers start finish full
      (C.closeIntervalTangentFan retain w c covers start finish
        (C.angularToTangent retain w c x)) = (C.linkAngularFan retain w c).develop x := by
  have angular_full := (C.linkAngularFan_totalAngle retain w c covers).trans full
  change (C.linkAngularFan retain w c).closedDevelop angular_full
    ((C.linkAngularFan retain w c).closeMap
      ((C.intervalFanIsometry retain w c covers start finish).symm
        (C.angularToTangent retain w c x))) = _
  rw [← C.intervalFanIsometry_apply retain w c covers start finish x,
    IsometryEquiv.symm_apply_apply, AngularFan.closedDevelop_closeMap]

end Unfoldings.TriangleComplex
