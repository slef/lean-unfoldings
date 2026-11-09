module

public import Unfoldings.Geometry.RaySection
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-! Positive radial slicing preserves the actual affine apex angle. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem angle_radialSlicePoint (f : E →L[ℝ] ℝ) (x y z : E) (h : ℝ)
    (level_positive : 0 < h) (left_positive : 0 < f (y - x))
    (right_positive : 0 < f (z - x)) :
    EuclideanGeometry.angle (radialSlicePoint f x h y) x (radialSlicePoint f x h z) =
      EuclideanGeometry.angle y x z := by
  simp only [EuclideanGeometry.angle, radialSlicePoint, vsub_eq_sub,
    AffineMap.lineMap_apply_module', add_sub_cancel_right]
  exact angle_radial_normalize f (y - x) (z - x) h
    level_positive left_positive right_positive

end Unfoldings
