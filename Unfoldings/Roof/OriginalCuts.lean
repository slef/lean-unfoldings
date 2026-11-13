module

public import Unfoldings.Roof.SelectionInteriorLabels

/-! Actual projected original cuts on arbitrary-rim roofs, including all seam endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The actual closed projected images of the cut original seams. -/
def projectedCutSet (retain : Set C.Seam) : Set Plane :=
  ⋃ s : C.Seam, ⋃ (_ : s ∉ retain),
    (K.projectedTriangle (C.left s).face).edge (C.left s).edge

/-- An interior point belongs to exactly its own original projected face. -/
theorem projected_face_unique_of_interior {f g : Face} {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier)
    (member : p ∈ (K.projectedTriangle g).carrier) : f = g := by
  by_contra different
  exact Set.disjoint_left.mp (K.projected_interior_disjoint_carrier different) inside member

/-- Every original seam avoids every original face interior. -/
theorem projected_seam_not_mem_face_interior (s : C.Seam) (f : Face) {p : Plane}
    (inside : p ∈ interior (K.projectedTriangle f).carrier) :
    p ∉ (K.projectedTriangle (C.left s).face).edge (C.left s).edge := by
  intro member
  have same := K.projected_face_unique_of_interior inside
    ((K.projectedTriangle (C.left s).face).edge_subset _ member)
  subst f
  exact (K.projectedTriangle (C.left s).face).not_mem_interior_of_mem_edge _ member inside

end Unfoldings.ConvexRoof
