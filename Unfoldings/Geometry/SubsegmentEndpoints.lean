module

public import Unfoldings.Geometry.SegmentVertices

/-! Finite whole-edge meshing preserves the endpoints of every genuine old segment. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem left_endpoint_of_subsegment {a b c d : E} (different : a ≠ b)
    (member : a ∈ segment ℝ c d) (subset : segment ℝ c d ⊆ segment ℝ a b) :
    a = c ∨ a = d := by
  let coordinate := lineCoordinate a b
  have at_start : coordinate a = 0 := by
    simpa only [AffineMap.lineMap_apply_zero] using lineCoordinate_lineMap different 0
  have first_on := subset (left_mem_segment ℝ c d)
  have last_on := subset (right_mem_segment ℝ c d)
  have first_line := segment_subset_line a b first_on
  have last_line := segment_subset_line a b last_on
  have nonnegative (x : E) (on_segment : x ∈ segment ℝ a b) : 0 ≤ coordinate x := by
    obtain ⟨s, bounds, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset on_segment
    change 0 ≤ lineCoordinate a b x
    rw [← at_x, lineCoordinate_lineMap different]
    exact bounds.1
  have in_interval := (lineCoordinate_mem_segment_iff different first_line last_line
    (left_mem_affineSpan_pair ℝ a b)).mp member
  have lower : min (coordinate c) (coordinate d) ≤ 0 := by
    have bound : min (coordinate c) (coordinate d) ≤ coordinate a := in_interval.1
    exact at_start ▸ bound
  rcases min_le_iff.mp lower with first | last
  · have zero : coordinate c = 0 := le_antisymm first (nonnegative c first_on)
    exact Or.inl (lineCoordinate_injective different first_line (left_mem_affineSpan_pair ℝ a b)
      (zero.trans at_start.symm)).symm
  · have zero : coordinate d = 0 := le_antisymm last (nonnegative d last_on)
    exact Or.inr (lineCoordinate_injective different last_line (left_mem_affineSpan_pair ℝ a b)
      (zero.trans at_start.symm)).symm

end Unfoldings
