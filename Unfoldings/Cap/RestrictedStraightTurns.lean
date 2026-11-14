module

public import Unfoldings.Cap.ProjectedPartialLink
public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Complex.LinkCornerWeights
public import Unfoldings.Polyhedron.RestrictedBoundaryTurns

/-! Straight projected boundary vertices have zero projected turn and controlled fan error. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  (U : Set Face)

open Classical in
/-- A straight boundary vertex has precisely a halfplane as its selected projected fan. -/
theorem restricted_projected_angle_eq_pi
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (straight : InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) = Real.pi) :
    (C.restrictFaces U).regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
      ((C.restrictFaces U).boundaryEndVertex Set.univ p) = Real.pi := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  obtain ⟨n, c, first, last, covers⟩ := R.exists_boundary_link Set.univ p
  let d := C.includeRestrictedLinkChain U c
  have projected_ray (g : R.LinkGerm Set.univ w) :
      K.projectedGermRay (C.includeRestrictedLinkGerm U g) =
        Cap.horizontal ((K.folding.restrictFaces U).germDirection g.val) :=
    (K.horizontal_germDirection (C.includeRestrictedLinkGerm U g)).symm
  have first_ray : K.projectedGermRay d.first =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) := by
    have same := projected_ray c.first
    rw [first] at same
    exact same
  have last_ray : K.projectedGermRay
      (C.linkTurn Set.univ (C.includeRestrictedVertexUniv U w) d.last) =
        Cap.horizontal ((K.folding.restrictFaces U).germDirection
          (R.boundaryMate Set.univ p).val) := by
    have same := projected_ray (R.linkTurn Set.univ w c.last)
    rw [last] at same
    exact same
  have selected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w c covers
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  obtain ⟨lower, upper⟩ := K.projected_partial_link_angle_bounds d internal
  rw [first_ray, last_ray, straight, selected] at lower upper
  rw [K.projectedTotalAngle_eq_two_pi _ internal] at upper
  exact le_antisymm (by linarith) lower

open Classical in
/-- Flat subdivision vertices on a straight connector require no separate corner or phase budget. -/
theorem abs_restricted_straight_turn_error_le_spatial_bend
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (straight : InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) = Real.pi) :
    |(Real.pi - (C.restrictFaces U).totalAngle Set.univ
        ((C.restrictFaces U).boundaryEndVertex Set.univ p)) -
      (Real.pi - (C.restrictFaces U).regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
        ((C.restrictFaces U).boundaryEndVertex Set.univ p))| ≤
      InnerProductGeometry.angle (-(K.folding.restrictFaces U).germDirection p.val)
        ((K.folding.restrictFaces U).germDirection
          ((C.restrictFaces U).boundaryMate Set.univ p).val) := by
  rw [K.restricted_projected_angle_eq_pi U p internal straight, sub_self, sub_zero]
  exact K.folding.abs_restricted_boundary_turn_le_spatial_bend U p internal
    (K.totalAngle_le_two_pi _ internal)

end Unfoldings.ConvexCap
