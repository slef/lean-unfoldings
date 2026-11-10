module

public import Unfoldings.Development.GermRays
public import Unfoldings.Geometry.Hinge
public import Unfoldings.Geometry.CornerDirections
public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.TriangleAffine

/-! Actual developed corner cones and separation at every retained hinge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

theorem place_affine_injective (f : Face) :
    Function.Injective (D.place f).toAffineEquiv.toAffineMap := (D.place f).injective

def placedTriangle (f : Face) : Triangle :=
  (C.triangle f).affineImage (D.place f).toAffineEquiv.toAffineMap (D.place_affine_injective f)

theorem placedTriangle_carrier (f : Face) : (D.placedTriangle f).carrier = D.faceImage f :=
  (C.triangle f).affineImage_carrier _ _

theorem germFaces_disjoint_of_crossing {p q : C.Germ} (crossing : C.GermCrosses retain p q) :
    Disjoint (interior (D.faceImage p.1.1)) (interior (D.faceImage q.1.1)) := by
  obtain ⟨s, kept, side, b, rfl, rfl⟩ := crossing
  cases side
  · exact D.hinge_nonoverlap s kept
  · exact (D.hinge_nonoverlap s kept).symm

theorem germRay_cone {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    strictRayCone (D.germRay p) (D.germRay (C.linkTurn retain v p)) =
      strictRayCone
        ((D.placedTriangle p.val.1.1).vertex (Triangle.next p.val.1.2) -
          (D.placedTriangle p.val.1.1).vertex p.val.1.2)
        ((D.placedTriangle p.val.1.1).vertex (Triangle.next (Triangle.next p.val.1.2)) -
          (D.placedTriangle p.val.1.1).vertex p.val.1.2) := by
  have apex := D.linkGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  cases side
  · change strictRayCone
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v)) = _
    rw [← apex]
    rfl
  · change strictRayCone
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v)) = _
    rw [← apex, strictRayCone_comm]
    rfl

theorem germRay_orient_ne_zero {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    orient 0 (D.germRay p) (D.germRay (C.linkTurn retain v p)) ≠ 0 := by
  have apex := D.linkGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  have identity (a b c : Plane) : orient 0 (b - a) (c - a) = orient a b c := by
    simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
  have reverse (a b c : Plane) : orient a c b = -orient a b c := by
    simp only [orient]
    ring
  cases side
  · change orient 0
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v)) ≠ 0
    rw [← apex, identity]
    exact (D.placedTriangle f).orient_edge_ne_zero i
  · change orient 0
      (D.place f ((C.triangle f).vertex (Triangle.next (Triangle.next i))) -
        D.toPlane (C.vertexPoint retain v))
      (D.place f ((C.triangle f).vertex (Triangle.next i)) - D.toPlane (C.vertexPoint retain v)) ≠ 0
    rw [← apex, identity, reverse]
    exact neg_ne_zero.mpr ((D.placedTriangle f).orient_edge_ne_zero i)

/-- Adjacent developed wedges are disjoint even when distant faces of the development overlap. -/
theorem germCones_disjoint_of_crossing {v : C.Vertex retain} (p q : C.LinkGerm retain v)
    (crossing : C.GermCrosses retain (C.turnGerm p.val) q.val) :
    Disjoint (strictRayCone (D.germRay p) (D.germRay (C.linkTurn retain v p)))
      (strictRayCone (D.germRay q) (D.germRay (C.linkTurn retain v q))) := by
  rw [D.germRay_cone, D.germRay_cone]
  apply (D.placedTriangle _).disjoint_cornerDirections (D.placedTriangle _) p.val.1.2 q.val.1.2
  · change D.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2) =
      D.place q.val.1.1 ((C.triangle q.val.1.1).vertex q.val.1.2)
    exact (D.linkGerm_apex p).trans (D.linkGerm_apex q).symm
  · rw [D.placedTriangle_carrier, D.placedTriangle_carrier]
    exact D.germFaces_disjoint_of_crossing (p := C.turnGerm p.val) (q := q.val) crossing

end Unfoldings.FacewiseDevelopment
