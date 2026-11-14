module

public import Unfoldings.Geometry.SegmentLineAvoidance

/-! Generic endpoint equations control entire extended connector lines. -/

@[expose] public section

namespace Unfoldings

/-- The entire extended connector line avoids the exceptional point. -/
theorem lineMap_ne_of_segmentEquation_ne_zero {a b q : Plane}
    (regular : segmentEquation a b q ≠ 0) (different : a ≠ b) (t : ℝ) :
    AffineMap.lineMap a q t ≠ b := by
  classical
  have area : orient a b q ≠ 0 := by
    simpa only [segmentEquation, ite_eq_right different, orientMap_apply] using regular
  exact lineMap_ne_of_orient_ne_zero area t


end Unfoldings
