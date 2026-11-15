module

public import Unfoldings.Complex.RestoredLinkChain
public import Unfoldings.Cone.IntervalIsometry

/-! Surviving terminal banks preserve the entire original intrinsic tangent fan and its cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  {w : C.Vertex small} {n : ℕ} (c : (C.linkSystem small w).Chain n)
  (covers : ∀ p, c.Visited p)
  (start : C.linkMate small w c.first = c.first)
  (finish : C.linkMate small w (C.linkTurn small w c.last) = C.linkTurn small w c.last)
  (first : C.IsBoundaryEdge large (C.germEdge c.first.val))
  (last : C.IsBoundaryEdge large (C.germEdge (C.turnGerm c.last.val)))

/-- A corner's entire original supporting wedge remains the same metric piece. -/
def restoreCorner (q : C.CornerAt small w) : C.CornerAt large (C.vertexForgetCuts inclusion w) :=
  ⟨q.val, congrArg (C.vertexForgetCuts inclusion) q.property⟩

/-- The unchanged ordered angular model identifies the two actual intrinsic tangent metrics. -/
def restoredBoundaryFanIsometry :
    C.TangentFan small w ≃ᵢ C.TangentFan large (C.vertexForgetCuts inclusion w) :=
  (C.intervalFanIsometry small w c covers start finish).symm.trans
    (C.intervalFanIsometry large (C.vertexForgetCuts inclusion w)
      (C.restoreLinkChain inclusion c) (C.restoreLinkChain_covers inclusion c first last)
      (Subtype.ext ((C.mateGerm_eq_self_iff large c.first.val).mpr first))
      (Subtype.ext ((C.mateGerm_eq_self_iff large (C.turnGerm c.last.val)).mpr last)))

/-- The common angular parameter preserves every original directed corner frame. -/
theorem restoredBoundaryFanIsometry_angularToTangent
    (x : (C.linkAngularFan small w c).Surface) :
    C.restoredBoundaryFanIsometry inclusion c covers start finish first last
      (C.angularToTangent small w c x) =
        C.angularToTangent large (C.vertexForgetCuts inclusion w)
          (C.restoreLinkChain inclusion c) x := by
  let E := C.intervalFanIsometry large (C.vertexForgetCuts inclusion w)
    (C.restoreLinkChain inclusion c) (C.restoreLinkChain_covers inclusion c first last)
    (Subtype.ext ((C.mateGerm_eq_self_iff large c.first.val).mpr first))
    (Subtype.ext ((C.mateGerm_eq_self_iff large (C.turnGerm c.last.val)).mpr last))
  change E ((C.intervalFanIsometry small w c covers start finish).symm
    ((C.intervalFanIsometry small w c covers start finish) x)) = E x
  rw [IsometryEquiv.symm_apply_apply]

/-- The isometry keeps each named original corner point, rather than choosing a new placement. -/
theorem restoredBoundaryFanIsometry_faceMap (q : C.CornerAt small w)
    (x : C.TangentCell small w q) :
    C.restoredBoundaryFanIsometry inclusion c covers start finish first last
      (C.tangentFaceMap small w q x) =
        C.tangentFaceMap large (C.vertexForgetCuts inclusion w)
          (C.restoreCorner inclusion q) x := by
  obtain ⟨i, rfl⟩ := (C.linkCornerEquiv small w c covers).surjective q
  let y : C.TangentCell small w (C.linkCornerAt small w c i) := x
  let z := (C.linkSectorIsometry small w c i) y
  let z' : (C.linkAngularFan large (C.vertexForgetCuts inclusion w)
    (C.restoreLinkChain inclusion c)).Cell i := z
  have angular := C.restoredBoundaryFanIsometry_angularToTangent inclusion c covers
    start finish first last ((C.linkAngularFan small w c).faceMap i z)
  rw [C.angularToTangent_faceMap] at angular
  change C.restoredBoundaryFanIsometry inclusion c covers start finish first last
      (C.linkCellToTangent small w c i z) =
    C.angularToTangent large (C.vertexForgetCuts inclusion w) (C.restoreLinkChain inclusion c)
      ((C.linkAngularFan large (C.vertexForgetCuts inclusion w)
        (C.restoreLinkChain inclusion c)).faceMap i z') at angular
  rw [C.angularToTangent_faceMap] at angular
  have left : C.linkCellToTangent small w c i z = C.tangentFaceMap small w _ y := by
    simp only [linkCellToTangent, z, IsometryEquiv.symm_apply_apply]
  have right : C.linkCellToTangent large (C.vertexForgetCuts inclusion w)
      (C.restoreLinkChain inclusion c) i z' =
        C.tangentFaceMap large (C.vertexForgetCuts inclusion w)
          (C.restoreCorner inclusion (C.linkCornerAt small w c i)) y := by
    let frame := ((C.triangle (c.point i).val.1.1).cornerFrame
      (c.point i).val.1.2).directedSectorIsometry (c.point i).val.2
    let point : (C.triangle (c.point i).val.1.1).cornerWedge (c.point i).val.1.2 := y
    have cancelled := frame.symm_apply_apply point
    exact congrArg (fun t : (C.triangle (c.point i).val.1.1).cornerWedge (c.point i).val.1.2 =>
      C.tangentFaceMap large (C.vertexForgetCuts inclusion w)
        (C.restoreCorner inclusion (C.linkCornerAt small w c i)) t) cancelled
  rw [left, right] at angular
  exact angular

end Unfoldings.TriangleComplex
