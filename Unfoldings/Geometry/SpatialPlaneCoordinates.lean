module

public import Unfoldings.Geometry.SupportedPlane

/-! Coplanar support pieces have exact rigid changes of their original plane coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialPlane

variable (P Q : SpatialPlane)

/-- Equal physical affine heights identify the entire spatial planes, not just their projections. -/
theorem place_change_coordinates (same : P.height = Q.height) (x : Plane) :
    Q.place (Q.project.symm (P.project x)) = P.place x := by
  have horizontal : Cap.horizontal (Q.place (Q.project.symm (P.project x))) =
      Cap.horizontal (P.place x) := by
    rw [Q.horizontal_place, Q.project.apply_symm_apply, P.horizontal_place]
  have vertical : Q.place (Q.project.symm (P.project x)) 2 = P.place x 2 := by
    rw [Q.height_place, Q.project.apply_symm_apply, ← same, P.height_place]
  ext j
  fin_cases j
  · exact congrArg (fun z : Plane => z 0) horizontal
  · exact congrArg (fun z : Plane => z 1) horizontal
  · exact vertical

/-- The original rigid face coordinates of coplanar supports are related by an affine isometry. -/
def coordinateEquiv (same : P.height = Q.height) : Plane ≃ᵃⁱ[ℝ] Plane := by
  let A := P.project.trans Q.project.symm
  have isometric : Isometry A := by
    intro x y
    have placed_x := P.place_change_coordinates Q same x
    have placed_y := P.place_change_coordinates Q same y
    change Q.place (A x) = P.place x at placed_x
    change Q.place (A y) = P.place y at placed_y
    rw [← Q.place.isometry.edist_eq, placed_x, placed_y, P.place.isometry.edist_eq]
  refine { A with norm_map := ?_ }
  intro x
  have linear := A.toAffineMap.linear_apply_vsub x 0
  change A.linear (x - 0) = A x - A 0 at linear
  rw [sub_zero] at linear
  rw [linear, ← dist_eq_norm, isometric.dist_eq, dist_zero_right]

@[simp] theorem coordinateEquiv_apply (same : P.height = Q.height) (x : Plane) :
    P.coordinateEquiv Q same x = Q.project.symm (P.project x) := rfl

@[simp] theorem place_coordinateEquiv (same : P.height = Q.height) (x : Plane) :
    Q.place (P.coordinateEquiv Q same x) = P.place x := by
  rw [coordinateEquiv_apply, P.place_change_coordinates Q same]

end Unfoldings.SpatialPlane
