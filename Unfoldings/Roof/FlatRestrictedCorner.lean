module

public import Unfoldings.Roof.SharpRestrictedCorners
public import Unfoldings.Roof.RestrictedBankRays

/-! At an actual flat corner, its projection error is exactly the error of its two rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {w : C.Vertex Set.univ}

/-- A flat support compares the two actual rays, including when the region
takes the reflex fan between them. -/
theorem abs_flat_link_projection_error_eq_angle {n : ℕ}
    (c : (C.linkSystem Set.univ w).Chain n)
    (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (f : Face) (slopes : ∀ g i, C.vertexOfCorner Set.univ (g, i) = w →
      K.normalSlope g = K.normalSlope f)
    (different : K.projectedGermRay (C.linkTurn Set.univ w c.last) ≠ K.projectedGermRay c.first) :
    |(∑ i, (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) -
      ∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2| =
      |angle (K.sectionDirection f (K.projectedGermRay c.first))
          (K.sectionDirection f (K.projectedGermRay (C.linkTurn Set.univ w c.last))) -
        angle (K.projectedGermRay c.first) (K.projectedGermRay (C.linkTurn Set.univ w c.last))| := by
  have short_error {m : ℕ} (d : (C.linkSystem Set.univ w).Chain m)
      (short : (∑ i, (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) ≤ π) :
      |(∑ i, (C.triangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) -
        ∑ i, (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2| =
        |angle (K.sectionDirection f (K.projectedGermRay d.first))
            (K.sectionDirection f (K.projectedGermRay (C.linkTurn Set.univ w d.last))) -
          angle (K.projectedGermRay d.first) (K.projectedGermRay (C.linkTurn Set.univ w d.last))| := by
    have halfplane := K.projectedInterval_halfplane_of_sum_le_pi d short
    rw [K.sum_flat_link_corner_angles d f (fun i => slopes _ _ (d.point i).property) halfplane,
      K.sum_projected_link_corner_angles d halfplane, K.projectedIntervalRay_last]
    have first : K.projectedIntervalRay d 0 = K.projectedGermRay d.first :=
      K.projectedIntervalRay_castSucc d 0
    rw [first]
  by_cases short : (∑ i, (K.projectedTriangle (c.point i).val.1.1).cornerAngle
      (c.point i).val.1.2) ≤ π
  · exact short_error c short
  have incident : K.incidentSlopes w ⊆ segment ℝ (K.normalSlope f) (K.normalSlope f) := by
    rintro x ⟨g, i, contact, rfl⟩
    rw [slopes g i contact]
    exact left_mem_segment ℝ _ _
  have zero := K.interiorCurvature_eq_zero_of_normalPolygon_collinear w
    ((collinear_segment _ _).subset (convexHull_min incident (convex_segment _ _)))
  have total : C.totalAngle Set.univ w = 2 * π := by
    simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal] at zero
    linarith
  obtain ⟨m, d, short_d, first_d, last_d, error⟩ :=
    K.exists_short_link_same_projection_error c internal total different (lt_of_not_ge short)
  rw [error, short_error d short_d, first_d, last_d]

open Classical in
/-- A flat restricted fan has the angle error of its two actual outgoing rays. -/
theorem abs_flat_restrictedBoundaryTurnError_eq_angle (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ (C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (f : Face) (slopes : ∀ g i, C.vertexOfCorner Set.univ (g, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope g = K.normalSlope f) :
    let R := C.restrictFaces U
    let F := K.folding.restrictFaces U
    let x := Cap.horizontal (F.germDirection p.val)
    let y := Cap.horizontal (F.germDirection (R.boundaryMate Set.univ p).val)
    |K.restrictedBoundaryTurnError U p| =
      |angle (K.sectionDirection f x) (K.sectionDirection f y) - angle x y| := by
  dsimp only
  obtain ⟨n, c, first_ray, last_ray, error⟩ := K.exists_restricted_link_with_projection_error U p
  rw [error, K.abs_flat_link_projection_error_eq_angle c internal f slopes, first_ray, last_ray]
  rw [first_ray, last_ray]
  intro equal
  have zero := K.restricted_boundary_rays_angle_ne_zero U p
  rw [← equal, angle_self] at zero
  · exact zero rfl
  · rw [← last_ray]
    exact K.projectedGermRay_ne_zero _

end Unfoldings.ConvexRoof
