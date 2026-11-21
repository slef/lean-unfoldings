module

public import Unfoldings.Geometry.SegmentEquation
public import Unfoldings.Geometry.Affine

/-! Finite regularity of the whole affine line used by a closing segment. -/

@[expose] public section

namespace Unfoldings

open Classical in
/-- Avoiding the line from an endpoint through a marked point rules out the
marked point on the whole new line, unless it is the fixed endpoint. -/
theorem eq_endpoint_of_lineMap_of_segmentEquation_ne_zero {a x b : Plane}
    (regular : segmentEquation a x b ≠ 0) (t : ℝ)
    (collinear : AffineMap.lineMap a b t = x) : x = a := by
  by_contra different
  apply regular
  rw [segmentEquation, ite_eq_right (Ne.symm different), orientMap_apply]
  have swap : orient a x b = -orient a b x := by
    simp only [orient]
    ring
  rw [swap, ← collinear, orient_lineMap, neg_zero]

end Unfoldings
