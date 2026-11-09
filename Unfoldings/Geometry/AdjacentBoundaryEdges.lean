module

public import Unfoldings.Geometry.BoundaryHalfplanes

/-!
# Consecutive simple convex boundary edges keep the same radial orientation

Supporting half-planes give consistent signs unless the three boundary
vertices are collinear. Open-edge separation handles that case too: only
the straight subdivision order can occur.
-/

@[expose] public section

namespace Unfoldings

theorem wbtw_of_collinear_disjoint_edges {a b c : Plane}
    (collinear : Collinear ℝ ({a, b, c} : Set Plane))
    (left : Disjoint (openSegment ℝ a b) (segment ℝ b c))
    (right : Disjoint (openSegment ℝ b c) (segment ℝ a b)) : Wbtw ℝ a b c := by
  rcases collinear.wbtw_or_wbtw_or_wbtw with between | back | back
  · exact between
  · have hc : c ∈ segment ℝ a b := by
      rw [segment_symm]
      exact back.mem_segment
    have included := (convex_segment a b).segment_subset (right_mem_segment ℝ a b) hc
    exact (Set.disjoint_left.mp right (midpoint_mem_openSegment b c)
      (included (midpoint_mem_segment b c))).elim
  · have ha : a ∈ segment ℝ b c := by
      rw [segment_symm]
      exact back.mem_segment
    have included := (convex_segment b c).segment_subset ha (left_mem_segment ℝ b c)
    exact (Set.disjoint_left.mp left (midpoint_mem_openSegment a b)
      (included (midpoint_mem_segment a b))).elim

theorem orient_mul_nonneg_of_wbtw {a b c : Plane} (between : Wbtw ℝ a b c) (x : Plane) :
    0 ≤ orient a b x * orient b c x := by
  obtain ⟨t, ht, image⟩ := between
  have formula : orient a b x * orient b c x =
      (t * (1 - t)) * (orient a c x) ^ 2 := by
    rw [← image, AffineMap.lineMap_apply_module']
    simp only [orient, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [formula]
  exact mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg _)

theorem orient_mul_pos_of_adjacent_boundary_edges {s : Set Plane}
    (convex : Convex ℝ s) (closed : IsClosed s) {a b c x : Plane}
    (inside : x ∈ interior s) (ab : a ≠ b) (bc : b ≠ c)
    (first : segment ℝ a b ⊆ frontier s) (second : segment ℝ b c ⊆ frontier s)
    (left : Disjoint (openSegment ℝ a b) (segment ℝ b c))
    (right : Disjoint (openSegment ℝ b c) (segment ℝ a b)) :
    0 < orient a b x * orient b c x := by
  have ane := orient_ne_zero_of_boundary_segment convex closed inside ab first
  have bne := orient_ne_zero_of_boundary_segment convex closed inside bc second
  by_cases straight : orient a b c = 0
  · have between := wbtw_of_collinear_disjoint_edges
      ((orient_eq_zero_iff_collinear a b c).mp straight) left right
    exact lt_of_le_of_ne (orient_mul_nonneg_of_wbtw between x) (mul_ne_zero ane bne).symm
  · have hc : c ∈ s := closed.closure_eq ▸ (second (right_mem_segment ℝ _ _)).1
    have ha : a ∈ s := closed.closure_eq ▸ (first (left_mem_segment ℝ _ _)).1
    have first_side := orient_mul_nonneg_of_boundary_segment convex closed inside ab first hc
    have second_side := orient_mul_nonneg_of_boundary_segment convex closed inside bc second ha
    rw [orient_cyclic] at second_side
    have first_pos := lt_of_le_of_ne first_side (mul_ne_zero straight ane).symm
    have second_pos := lt_of_le_of_ne second_side (mul_ne_zero straight bne).symm
    have product := mul_pos first_pos second_pos
    have identity : (orient a b c * orient a b x) * (orient a b c * orient b c x) =
        (orient a b c) ^ 2 * (orient a b x * orient b c x) := by ring
    rw [identity] at product
    rcases mul_pos_iff.mp product with ⟨_, positive⟩ | ⟨negative, _⟩
    · exact positive
    · exact ((sq_nonneg _).not_gt negative).elim

end Unfoldings
