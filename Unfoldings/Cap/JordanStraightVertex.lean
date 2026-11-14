module

public import Unfoldings.Cap.RestrictedStraightTurns
public import Unfoldings.Cap.JordanBankTurnBounds

/-! Spatial bends bound the actual fan-turn error at straight Jordan bank vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- This is the actual real fan error from the intrinsic/projected contour comparison. -/
theorem abs_jordan_straight_vertex_error_le_spatial_bend (inside : J ⊆ interior K.footprint)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (straight :
      let p := (K.jordanContour jordan contains avoids).cycle.point i
      let F := K.folding.restrictFaces (K.jordanFaces J)
      InnerProductGeometry.angle (Cap.horizontal (F.germDirection p.val))
        (Cap.horizontal (F.germDirection
          ((C.restrictFaces (K.jordanFaces J)).boundaryMate Set.univ p).val)) = Real.pi) :
    |K.jordanContourTurnError jordan contains avoids i| ≤
      let p := (K.jordanContour jordan contains avoids).cycle.point i
      let F := K.folding.restrictFaces (K.jordanFaces J)
      InnerProductGeometry.angle (-F.germDirection p.val)
        (F.germDirection ((C.restrictFaces (K.jordanFaces J)).boundaryMate Set.univ p).val) := by
  let R := C.restrictFaces (K.jordanFaces J)
  let p := (K.jordanContour jordan contains avoids).cycle.point i
  let w := R.boundaryEndVertex Set.univ p
  let original := C.includeRestrictedVertexUniv (K.jordanFaces J) w
  have on_curve : K.projectedVertex original ∈ J :=
    (K.jordan_isBoundaryVertex_iff jordan contains avoids w).mp
      (R.boundaryEndAsVertex Set.univ p).property
  have internal : ¬ C.IsBoundaryVertex Set.univ original :=
    (K.projectedVertex_mem_interior_iff original).mp (inside on_curve)
  exact K.abs_restricted_straight_turn_error_le_spatial_bend (K.jordanFaces J) p internal straight

end Unfoldings.ConvexCap
