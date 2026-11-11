module

public import Unfoldings.Cap.CompletedParentBankOpening
public import Unfoldings.Cap.ParentBankSides

/-! Actual completed-bank section crossing signs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {R : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C R.completedRetain}
  {e : {v : C.Vertex Set.univ // v ∉ R.spanningCompletion.parents.roots}} (B : R.ParentBankOpening
    D e)

/-- Positive outward determinant gives the actual positive curvature phase at the entrance. -/
theorem entrance_crossing_sign {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (first_face : T.face i.castSucc = B.entranceFace)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (R.spanningCompletion.selection.edge e)).face).edge
        (C.left (R.spanningCompletion.selection.edge e)).edge) :
    0 < orient 0
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val) (q
        - p) := by
  let bank := R.completedContour.cycle.point B.enter
  have positive := D.projectedGermOrientation_cycle_positive K R.completedDuallyConnected
    R.completedContour.cycle R.completedContour_positive B.enter
  have named := congrArg Subtype.val B.first_named
  have edge := K.projected_bank_edge_eq bank (R.spanningCompletion.selection.edge e) B.side named
  have cross : T.point i.castSucc.succ ∈
      (K.projectedTriangle bank.val.1.1).edge (C.germEdge bank.val).edge := edge.symm ▸ crossing
  have sign := T.bank_exit_sign different regular i bank.val first_face positive cross
  rw [K.projectedGermVector_parent_entrance R.spanningCompletion.selection e.val e.property
    bank B.side B.first_named B.outside] at sign
  have reverse (a b : Plane) : orient 0 (-a) b = -orient 0 a b := by
    simp only [orient, PiLp.neg_apply, PiLp.zero_apply, sub_zero]
    ring
  rw [reverse] at sign
  exact neg_neg_iff_pos.mp sign

/-- Negative outward determinant gives the actual negative curvature phase in reverse. -/
theorem exit_crossing_sign {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (first_face : T.face i.castSucc = B.exitFace)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left (R.spanningCompletion.selection.edge e)).face).edge
        (C.left (R.spanningCompletion.selection.edge e)).edge) :
    orient 0
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val) - K.projectedVertex e.val) (q
        - p) < 0 := by
  let bank := R.completedContour.cycle.point B.leave
  have positive := D.projectedGermOrientation_cycle_positive K R.completedDuallyConnected
    R.completedContour.cycle R.completedContour_positive B.leave
  have named := congrArg Subtype.val B.last_named
  have edge := K.projected_bank_edge_eq bank (R.spanningCompletion.selection.edge e) (!B.side) named
  have cross : T.point i.castSucc.succ ∈
      (K.projectedTriangle bank.val.1.1).edge (C.germEdge bank.val).edge := edge.symm ▸ crossing
  have sign := T.bank_exit_sign different regular i bank.val first_face positive cross
  rwa [K.projectedGermVector_parent_exit R.spanningCompletion.selection e.val e.property
    bank (!B.side) B.last_named B.inside] at sign

end Unfoldings.ConvexCap.RadialCutForest.ParentBankOpening
