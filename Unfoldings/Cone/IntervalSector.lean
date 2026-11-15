module

public import Unfoldings.Cone.IntervalIsometry
public import Unfoldings.Cone.ReentrantSector

/-! Actual retained interval fans have their geometric intrinsic sector metrics. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (w : C.Vertex retain) {n : ℕ}
  (c : (C.linkSystem retain w).Chain n) (covers : ∀ p, c.Visited p)
  (start : C.linkMate retain w c.first = c.first)
  (finish : C.linkMate retain w (C.linkTurn retain w c.last) = C.linkTurn retain w c.last)
  (small : C.totalAngle retain w < 2 * Real.pi)

/-- No convexity assumption on the whole retained corner is needed. -/
def intervalSectorIsometryEquiv :
    C.TangentFan retain w ≃ᵢ PolygonalPoint (closedAngularSector (C.totalAngle retain w)) :=
  ((C.intervalFanIsometry retain w c covers start finish).symm.trans
    ((C.linkAngularFan retain w c).intrinsicAngularSectorIsometryEquiv
      (by rwa [C.linkAngularFan_totalAngle retain w c covers]))).trans
        (PolygonalPoint.congrIsometryEquiv (by rw [C.linkAngularFan_totalAngle retain w c covers]))

@[simp] theorem intervalSectorIsometryEquiv_angularToTangent
    (z : (C.linkAngularFan retain w c).Surface) :
    (C.intervalSectorIsometryEquiv retain w c covers start finish small
      (C.angularToTangent retain w c z)).val = (C.linkAngularFan retain w c).develop z := by
  change (PolygonalPoint.congrIsometryEquiv _
    (((C.linkAngularFan retain w c).intrinsicAngularSectorIsometryEquiv _)
      ((C.intervalFanIsometry retain w c covers start finish).symm
        ((C.intervalFanIsometry retain w c covers start finish) z)))).val = _
  rw [IsometryEquiv.symm_apply_apply, PolygonalPoint.congrIsometryEquiv_val,
    AngularFan.intrinsicAngularSectorIsometryEquiv_val]

@[simp] theorem intervalSectorIsometryEquiv_origin :
    (C.intervalSectorIsometryEquiv retain w c covers start finish small
      (C.tangentOrigin retain w)).val = 0 := by
  rw [← C.angularToTangent_origin retain w c,
    C.intervalSectorIsometryEquiv_angularToTangent, AngularFan.develop_origin]

end Unfoldings.TriangleComplex
