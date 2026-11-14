module

public import Unfoldings.Cap.JordanBoundary
public import Unfoldings.Polyhedron.RestrictedBoundaryTurns

/-! Actual intrinsic Jordan bank turns contract spatial turning at every original vertex copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J)
  (inside : J ⊆ interior K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan inside avoids in
open Classical in
/-- The real exterior fan turn is controlled even at arbitrary-valence subdivision vertices. -/
theorem abs_jordan_vertex_turn_le_spatial_bend
    (p : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ) :
    |Real.pi - (C.restrictFaces (K.jordanFaces J)).totalAngle Set.univ
      ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ p)| ≤
      InnerProductGeometry.angle
        (-(K.folding.restrictFaces (K.jordanFaces J)).germDirection p.val)
        ((K.folding.restrictFaces (K.jordanFaces J)).germDirection
          ((C.restrictFaces (K.jordanFaces J)).boundaryMate Set.univ p).val) := by
  let R := C.restrictFaces (K.jordanFaces J)
  let w := R.boundaryEndVertex Set.univ p
  let original := C.includeRestrictedVertexUniv (K.jordanFaces J) w
  have on_curve : K.projectedVertex original ∈ J :=
    (K.jordan_isBoundaryVertex_iff jordan (inside.trans interior_subset) avoids w).mp
      (R.boundaryEndAsVertex Set.univ p).property
  have internal : ¬ C.IsBoundaryVertex Set.univ original :=
    (K.projectedVertex_mem_interior_iff original).mp (inside on_curve)
  exact K.folding.abs_restricted_boundary_turn_le_spatial_bend (K.jordanFaces J) p internal
    (K.totalAngle_le_two_pi original internal)

end Unfoldings.ConvexCap
