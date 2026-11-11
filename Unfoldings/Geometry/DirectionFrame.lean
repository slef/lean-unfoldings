module

public import Unfoldings.Geometry.Affine

/-! Orthogonal planar coordinates sending a prescribed direction to the positive horizontal ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Zero is fixed; every genuine prescribed direction points along the positive horizontal axis. -/
def directionFrame (direction : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  (twoPointIsometry 0 direction 0 (EuclideanSpace.single 0 ‖direction‖)).linearIsometryEquiv

theorem directionFrame_apply (direction : Plane) :
    directionFrame direction direction = EuclideanSpace.single 0 ‖direction‖ := by
  let target : Plane := EuclideanSpace.single 0 ‖direction‖
  have norm_target : ‖target‖ = ‖direction‖ := by
    simp only [target, EuclideanSpace.single, PiLp.norm_single, norm_norm]
  have same : dist (0 : Plane) direction = dist (0 : Plane) target := by
    rw [dist_zero_left, dist_zero_left, norm_target]
  have mapped := twoPointIsometry_right 0 direction 0 target same
  have linear := (twoPointIsometry 0 direction 0 target).map_vsub direction 0
  simp only [vsub_eq_sub, sub_zero, twoPointIsometry_left] at linear
  exact linear.trans mapped

@[simp] theorem directionFrame_horizontal (direction : Plane) :
    directionFrame direction direction 0 = ‖direction‖ := by
  rw [directionFrame_apply]
  simp [EuclideanSpace.single]

@[simp] theorem directionFrame_vertical (direction : Plane) :
    directionFrame direction direction 1 = 0 := by
  rw [directionFrame_apply]
  simp [EuclideanSpace.single]

/-- A section's horizontal coordinate is its real parameter times its actual length. -/
theorem directionFrame_lineMap_horizontal (p q : Plane) (t : ℝ) :
    directionFrame (q - p) (AffineMap.lineMap p q t - p) 0 = t * ‖q - p‖ := by
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change t * directionFrame (q - p) (q - p) 0 = _
  rw [directionFrame_horizontal]

/-- The whole actual section line has zero transverse coordinate. -/
theorem directionFrame_lineMap_vertical (p q : Plane) (t : ℝ) :
    directionFrame (q - p) (AffineMap.lineMap p q t - p) 1 = 0 := by
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change t * directionFrame (q - p) (q - p) 1 = 0
  rw [directionFrame_vertical, mul_zero]

end Unfoldings
