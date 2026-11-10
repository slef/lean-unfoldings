module

public import Unfoldings.Cap.AngleBalance
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Polyhedron.GermSpatial
public import Unfoldings.Complex.LinkOrdering
public import Unfoldings.Geometry.CornerDirections

/-! Actual projected rays and disjoint direction cones of a cap vertex link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The actual horizontal direction of a corner germ, based at its original vertex. -/
def projectedGermRay {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) : Plane :=
  Cap.horizontal (K.folding.germFarPoint p.val) - K.projectedVertex v

theorem projectedGerm_apex {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) :
    (K.projectedTriangle p.val.1.1).vertex p.val.1.2 = K.projectedVertex v :=
  congrArg Cap.horizontal (K.folding.linkGerm_apex Set.univ v p)

@[simp] theorem projectedGermRay_mate {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) :
    K.projectedGermRay (C.linkMate Set.univ v p) = K.projectedGermRay p := by
  change Cap.horizontal (K.folding.germFarPoint (C.mateGerm Set.univ p.val)) - _ = _
  rw [K.folding.germFarPoint_mate]
  rfl

theorem projectedGermRay_cone {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) :
    strictRayCone (K.projectedGermRay p) (K.projectedGermRay (C.linkTurn Set.univ v p)) =
      strictRayCone
        ((K.projectedTriangle p.val.1.1).vertex (Triangle.next p.val.1.2) -
          (K.projectedTriangle p.val.1.1).vertex p.val.1.2)
        ((K.projectedTriangle p.val.1.1).vertex (Triangle.next (Triangle.next p.val.1.2)) -
          (K.projectedTriangle p.val.1.1).vertex p.val.1.2) := by
  have apex := K.projectedGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  cases side
  · change strictRayCone
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v) = _
    rw [← apex]
  · change strictRayCone
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v) = _
    rw [← apex, strictRayCone_comm]

theorem projectedGermRay_angle {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) :
    InnerProductGeometry.angle (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ v p)) =
        (K.projectedTriangle p.val.1.1).cornerAngle p.val.1.2 := by
  have apex := K.projectedGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  cases side
  · change InnerProductGeometry.angle
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v) = _
    rw [← apex]
    rfl
  · change InnerProductGeometry.angle
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v) = _
    rw [← apex, InnerProductGeometry.angle_comm]
    rfl

include K in
theorem cornerAt_face_injective (v : C.Vertex Set.univ) :
    Function.Injective (fun c : C.CornerAt Set.univ v => c.val.1) := by
  intro a b same
  apply Subtype.ext
  apply Prod.ext same
  obtain ⟨⟨f, i⟩, ha⟩ := a
  obtain ⟨⟨g, j⟩, hb⟩ := b
  change f = g at same
  subst g
  have left : (K.projectedTriangle f).vertex i = K.projectedVertex v :=
    congrArg K.projectedVertex ha
  have right : (K.projectedTriangle f).vertex j = K.projectedVertex v :=
    congrArg K.projectedVertex hb
  exact (K.projectedTriangle f).vertex_injective (left.trans right.symm)

variable {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

theorem projectedGermRay_chain_rotates
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    K.projectedGermRay (C.linkTurn Set.univ v (c.point i)) =
      K.projectedGermRay (c.point (finRotate (n + 1) i)) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [finRotate_last]
    have equal := congrArg K.projectedGermRay closes
    change K.projectedGermRay (C.linkMate Set.univ v
      (C.linkTurn Set.univ v (c.point (Fin.last n)))) = K.projectedGermRay (c.point 0) at equal
    simpa only [K.projectedGermRay_mate] using equal
  · have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
    rw [rotated]
    have equal := congrArg K.projectedGermRay (c.next k)
    change K.projectedGermRay (C.linkMate Set.univ v
      (C.linkTurn Set.univ v (c.point k.castSucc))) = _ at equal
    simpa only [K.projectedGermRay_mate] using equal

/-- The projected fan uses the same actual ordered corner classes as the intrinsic link. -/
def projectedLinkFan : AngularFan n where
  angle i := (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2
  positive _ := (K.projectedTriangle _).cornerAngle_pos _
  small _ := (K.projectedTriangle _).cornerAngle_lt_pi _

theorem projectedLinkFan_ray_angle
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    InnerProductGeometry.angle (K.projectedGermRay (c.point i))
      (K.projectedGermRay (c.point (finRotate (n + 1) i))) = (K.projectedLinkFan c).angle i := by
  rw [← K.projectedGermRay_chain_rotates c closes i]
  exact K.projectedGermRay_angle (c.point i)

/-- Every ordered corner occurs once, even with repeated coplanar face normals. -/
theorem projectedLinkFan_totalAngle (covers : ∀ p, c.Visited p) :
    (K.projectedLinkFan c).totalAngle = K.projectedTotalAngle Set.univ v := by
  classical
  have subtype_sum : K.projectedTotalAngle Set.univ v =
      ∑ a : C.CornerAt Set.univ v, (K.projectedTriangle a.val.1).cornerAngle a.val.2 := by
    exact (Finset.sum_filter _ _).symm.trans
      (Finset.sum_subtype (Finset.univ.filter (fun a => C.vertexOfCorner Set.univ a = v))
        (by simp) (fun a : C.Corner => (K.projectedTriangle a.1).cornerAngle a.2))
  rw [subtype_sum]
  exact (C.linkCornerEquiv Set.univ v c covers).sum_comp
    (fun a : C.CornerAt Set.univ v => (K.projectedTriangle a.val.1).cornerAngle a.val.2)

/-- The open projected direction cones of distinct incident faces are actually disjoint. -/
theorem projectedLinkFan_cones_disjoint
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    Pairwise (fun i j => Disjoint
      (strictRayCone (K.projectedGermRay (c.point i))
        (K.projectedGermRay (c.point (finRotate (n + 1) i))))
      (strictRayCone (K.projectedGermRay (c.point j))
        (K.projectedGermRay (c.point (finRotate (n + 1) j))))) := by
  intro i j different
  rw [← K.projectedGermRay_chain_rotates c closes i,
    ← K.projectedGermRay_chain_rotates c closes j,
    K.projectedGermRay_cone, K.projectedGermRay_cone]
  have face_ne : (c.point i).val.1.1 ≠ (c.point j).val.1.1 := by
    intro equal
    apply different
    apply (C.linkCornerEquiv Set.univ v c covers).injective
    apply K.cornerAt_face_injective v
    exact equal
  apply (K.projectedTriangle _).disjoint_cornerDirections (K.projectedTriangle _)
    (c.point i).val.1.2 (c.point j).val.1.2
  · exact (K.projectedGerm_apex (c.point i)).trans (K.projectedGerm_apex (c.point j)).symm
  · exact K.projectedTriangles_nonoverlapping face_ne

end Unfoldings.ConvexCap
