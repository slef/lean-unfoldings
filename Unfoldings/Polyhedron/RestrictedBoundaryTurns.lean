module

public import Unfoldings.Complex.FaceRestrictionLinks
public import Unfoldings.Complex.BoundaryLink
public import Unfoldings.Polyhedron.LinkFanTurn
public import Unfoldings.Roof.FaceRestriction

/-! The actual one-sided boundary fan turn is bounded by its original spatial bend. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (U : Set Face)

open Classical in
/-- This includes reflex fans, arbitrary valence and new flat vertices on subdivided creases. -/
theorem abs_restricted_boundary_turn_le_spatial_bend
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (convex : C.totalAngle Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)) ≤
      2 * Real.pi) :
    |Real.pi - (C.restrictFaces U).totalAngle Set.univ
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)| ≤
      InnerProductGeometry.angle (-(F.restrictFaces U).germDirection p.val)
        ((F.restrictFaces U).germDirection ((C.restrictFaces U).boundaryMate Set.univ p).val) := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  obtain ⟨n, c, first, last, covers⟩ := R.exists_boundary_link Set.univ p
  let d := C.includeRestrictedLinkChain U c
  have selected_angle :
      (∑ i : Fin (n + 1), (C.triangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) =
        R.totalAngle Set.univ w := R.sum_linkCornerAngle Set.univ w c covers
  have first_ray : F.germDirection d.first.val = (F.restrictFaces U).germDirection p.val := by
    change F.germDirection (C.includeRestrictedGerm U c.first.val) = _
    rw [first]
    rfl
  have last_ray :
      F.germDirection (C.linkTurn Set.univ (C.includeRestrictedVertexUniv U w) d.last).val =
      (F.restrictFaces U).germDirection (R.boundaryMate Set.univ p).val := by
    change F.germDirection (C.includeRestrictedGerm U (R.linkTurn Set.univ w c.last).val) = _
    rw [last]
    rfl
  have estimate := F.abs_link_exterior_turn_le_spatial_bend d internal convex
  rw [selected_angle, first_ray, last_ray] at estimate
  exact estimate

end Unfoldings.SpatialFolding
