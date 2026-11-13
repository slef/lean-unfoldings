module

public import Unfoldings.Geometry.SupportedPlane

/-! Gnomonic slopes and exact height differences of rigid spatial support planes. -/

@[expose] public section

namespace Unfoldings.SpatialPlane

noncomputable def normalSlope (P : SpatialPlane) : Plane :=
  (P.normal 2)⁻¹ • Cap.horizontal P.normal

theorem height_difference (P : SpatialPlane) (p q : Plane) :
    P.height q = P.height p - inner ℝ P.normalSlope (q - p) := by
  rw [P.height_formula, P.height_formula]
  simp only [normalSlope, real_inner_smul_left, inner_sub_right]
  ring

end Unfoldings.SpatialPlane
