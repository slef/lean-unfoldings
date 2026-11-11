module

public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Geometry.SharedEdgeOpening

/-! Actual cap projection opens each original seam to strictly opposite sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Original seam banks have exactly the same whole projected geometric edge. -/
theorem projected_seam_edges_eq (s : C.Seam) :
    (K.projectedTriangle (C.left s).face).edge (C.left s).edge =
      (K.projectedTriangle (C.right s).face).edge (C.right s).edge := by
  rw [projectedTriangle, projectedTriangle, Triangle.affineImage_edge, Triangle.affineImage_edge]
  apply Set.Subset.antisymm
  · rintro z ⟨x, member, image⟩
    let a : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨x, member⟩
    exact ⟨(C.identify s a).val, (C.identify s a).property,
      (K.projectedTriangle_joined s a).symm.trans image⟩
  · rintro z ⟨y, member, image⟩
    let b : (C.triangle (C.right s).face).Edge (C.right s).edge := ⟨y, member⟩
    let a := (C.identify s).symm b
    have joined := K.projectedTriangle_joined s a
    have inverse := congrArg (fun w : (C.triangle (C.right s).face).Edge (C.right s).edge =>
      K.projectFace (C.right s).face w.val) ((C.identify s).apply_symm_apply b)
    exact ⟨a.val, a.property, joined.trans (inverse.trans image)⟩

/-- The original projected pair satisfies the same strict side convention as a development. -/
theorem projected_opposite (s : C.Seam) :
    orient ((K.projectedTriangle (C.left s).face).vertex (C.left s).edge)
      ((K.projectedTriangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
      ((K.projectedTriangle (C.left s).face).opposite (C.left s).edge) *
    orient ((K.projectedTriangle (C.left s).face).vertex (C.left s).edge)
      ((K.projectedTriangle (C.left s).face).vertex (Triangle.next (C.left s).edge))
      ((K.projectedTriangle (C.right s).face).opposite (C.right s).edge) < 0 :=
  (K.projectedTriangle (C.left s).face).opposite_of_shared_edge
    (K.projectedTriangle (C.right s).face) (C.left s).edge (C.right s).edge
    (K.projected_seam_edges_eq s)
    (K.projectedTriangles_nonoverlapping (K.folding.incident_faces_ne s))

end Unfoldings.ConvexCap
