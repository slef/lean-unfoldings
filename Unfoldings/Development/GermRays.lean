module

public import Unfoldings.Development
public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Complex.LinkOrdering
public import Unfoldings.Geometry.Angles

/-! Actual planar edge rays in a development, including developments with overlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

def germFarPoint (p : C.Germ) : Plane :=
  D.place p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2)

theorem linkGerm_apex {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    D.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2) =
      D.toPlane (C.vertexPoint retain v) :=
  congrArg (fun w : C.Vertex retain => D.toPlane (C.vertexPoint retain w)) p.property

theorem place_across (s : C.Seam) (kept : s ∈ retain) (side : Bool)
    (x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge) :
    D.place (C.seamSide s side).face x.val =
      D.place (C.seamSide s (!side)).face (C.across s side x).val := by
  cases side
  · exact D.joined s kept x
  · have equal := D.joined s kept ((C.identify s).symm x)
    exact (equal.trans (congrArg
      (fun y : (C.triangle (C.right s).face).Edge (C.right s).edge =>
        D.place (C.right s).face y.val) ((C.identify s).apply_symm_apply x))).symm

theorem germFarPoint_germOfEndpoint (e : EdgeRef Face) (b : Bool) :
    D.germFarPoint (C.germOfEndpoint e b) =
      D.place e.face ((C.triangle e.face).endpoint e.edge (!b)).val := by
  change D.place e.face ((C.triangle e.face).vertex
    (C.germFarCorner (C.germOfEndpoint e b)).2) = _
  rw [C.germFarCorner_germOfEndpoint]
  cases b <;> rfl

theorem germFarPoint_of_crossing {p q : C.Germ} (crossing : C.GermCrosses retain p q) :
    D.germFarPoint p = D.germFarPoint q := by
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  rw [D.germFarPoint_germOfEndpoint, D.germFarPoint_germOfEndpoint,
    ← C.acrossEndpoint_not, C.endpoint_acrossEndpoint]
  exact D.place_across s kept side ((C.triangle (C.seamSide s side).face).endpoint
    (C.seamSide s side).edge (!b))

theorem germFarPoint_mate (p : C.Germ) :
    D.germFarPoint (C.mateGerm retain p) = D.germFarPoint p := by
  classical
  by_cases paired : ∃ q, C.GermCrosses retain p q
  · obtain ⟨q, crossing⟩ := paired
    rw [C.mateGerm_of_crossing crossing]
    exact (D.germFarPoint_of_crossing crossing).symm
  · simp only [TriangleComplex.mateGerm, dite_eq_right paired]

def germRay {v : C.Vertex retain} (p : C.LinkGerm retain v) : Plane :=
  D.germFarPoint p.val - D.toPlane (C.vertexPoint retain v)

@[simp] theorem germRay_mate {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    D.germRay (C.linkMate retain v p) = D.germRay p := by
  change D.germFarPoint (C.mateGerm retain p.val) - _ = _
  rw [D.germFarPoint_mate]
  rfl

theorem germRay_ne_zero {v : C.Vertex retain} (p : C.LinkGerm retain v) : D.germRay p ≠ 0 := by
  rw [germRay, ← D.linkGerm_apex p]
  apply sub_ne_zero.mpr
  intro equal
  have corners := (C.triangle p.val.1.1).vertex_injective ((D.place p.val.1.1).injective equal)
  exact C.germFarCorner_ne p.val (Prod.ext rfl corners)

theorem germRay_angle {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    InnerProductGeometry.angle (D.germRay p) (D.germRay (C.linkTurn retain v p)) =
      (C.triangle p.val.1.1).cornerAngle p.val.1.2 := by
  have apex := D.linkGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  cases side
  · change InnerProductGeometry.angle
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v)) = _
    rw [← apex]
    exact (D.place f).toAffineIsometry.angle_map _ _ _
  · change InnerProductGeometry.angle
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v)) = _
    rw [← apex]
    exact ((D.place f).toAffineIsometry.angle_map _ _ _).trans (EuclideanGeometry.angle_comm _ _ _)

end Unfoldings.FacewiseDevelopment
