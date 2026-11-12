module

public import Unfoldings.Cap.ProjectedCoherence

/-! Projected face interiors select a unique containing face, even on the closed mesh. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem projectedTriangle_face_eq_of_interior {f g : Face} {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier)
    (member : p ∈ (K.projectedTriangle g).carrier) : f = g := by
  by_contra different
  let T := K.projectedTriangle g
  have regular := T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior
    T.interior_nonempty
  rw [(K.projectedTriangle g).compact_carrier.isClosed.closure_eq] at regular
  have separate := (K.projectedTriangles_nonoverlapping different).closure_right isOpen_interior
  rw [regular] at separate
  exact Set.disjoint_left.mp separate inside member

end Unfoldings.ConvexCap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

theorem projected_coherentAt_face_interior {f : Face} {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier) : D.ProjectedCoherentAt K p := by
  intro g h first last
  have fg := K.projectedTriangle_face_eq_of_interior inside first
  have fh := K.projectedTriangle_face_eq_of_interior inside last
  subst g
  subst h
  rfl

theorem projectedMap_eq_on_face_interior {f : Face} {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier) :
    D.projectedMap K p = D.projectedPlacement K f p :=
  D.projectedMap_eq_of_coherent K (D.projected_coherentAt_face_interior K inside)
    (interior_subset inside)

end Unfoldings.FacewiseDevelopment
