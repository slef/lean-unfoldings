module

public import Unfoldings.Development.GermRays
public import Unfoldings.Complex.BoundaryOrdering

/-! Actual directed bank vectors and reversal at the far endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

def boundaryRay (p : C.BoundaryEnd retain) : Plane :=
  D.germRay (⟨p.val, rfl⟩ : C.LinkGerm retain (C.boundaryEndVertex retain p))

theorem boundaryRay_eq_raw (p : C.BoundaryEnd retain) :
    D.boundaryRay p = D.germFarPoint p.val -
      D.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2) := by
  change D.germFarPoint p.val -
    D.toPlane (C.vertexPoint retain (C.boundaryEndVertex retain p)) = _
  rw [← D.linkGerm_apex
    (⟨p.val, rfl⟩ : C.LinkGerm retain (C.boundaryEndVertex retain p))]

theorem germRay_eq_boundaryRay {w : C.Vertex retain} (r : C.LinkGerm retain w)
    (p : C.BoundaryEnd retain) (same : r.val = p.val) : D.germRay r = D.boundaryRay p := by
  have vertex : w = C.boundaryEndVertex retain p :=
    r.property.symm.trans (congrArg (fun q : C.Germ => C.vertexOfCorner retain q.1) same)
  subst w
  exact congrArg D.germRay (Subtype.ext same)

theorem boundaryRay_ne_zero (p : C.BoundaryEnd retain) : D.boundaryRay p ≠ 0 :=
  D.germRay_ne_zero _

/-- This is reversal of the very same developed edge, with both its length and direction. -/
@[simp] theorem boundaryRay_turn (p : C.BoundaryEnd retain) :
    D.boundaryRay (C.boundaryTurn retain p) = -D.boundaryRay p := by
  obtain ⟨⟨bank, b⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  simp only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply, D.boundaryRay_eq_raw]
  change D.germFarPoint (C.germOfEndpoint bank.val (!b)) -
      D.place bank.val.face ((C.triangle bank.val.face).vertex
        (C.germOfEndpoint bank.val (!b)).1.2) =
    -(D.germFarPoint (C.germOfEndpoint bank.val b) -
      D.place bank.val.face ((C.triangle bank.val.face).vertex
        (C.germOfEndpoint bank.val b).1.2))
  rw [D.germFarPoint_germOfEndpoint, D.germFarPoint_germOfEndpoint]
  cases b <;> exact (neg_sub _ _).symm

end Unfoldings.FacewiseDevelopment
