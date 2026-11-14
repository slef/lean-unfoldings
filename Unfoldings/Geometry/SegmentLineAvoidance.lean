module

public import Unfoldings.Geometry.SegmentEquation

/-! Proper segment equations select endpoint directions that avoid prescribed vertices. -/

@[expose] public section

namespace Unfoldings

theorem ne_of_segmentEquation_ne_zero {a b q : Plane}
    (regular : segmentEquation a b q ≠ 0) : q ≠ b := by
  intro same
  rw [same] at regular
  exact regular (segmentEquation_eq_zero (right_mem_segment ℝ a b))

/-- Only the fixed endpoint can be exceptional; the entire rest of the connector avoids b. -/
theorem eq_endpoint_of_mem_segment_of_segmentEquation_ne_zero {a b q : Plane}
    (regular : segmentEquation a b q ≠ 0) (member : b ∈ segment ℝ a q) : b = a := by
  classical
  by_contra different
  have distinct : a ≠ b := Ne.symm different
  have orient_nonzero : orient a b q ≠ 0 := by
    simpa only [segmentEquation, ite_eq_right distinct, orientMap_apply] using regular
  rw [segment_eq_image_lineMap] at member
  obtain ⟨t, _, same⟩ := member
  exact lineMap_ne_of_orient_ne_zero orient_nonzero t same

end Unfoldings
