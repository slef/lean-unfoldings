module

public import Unfoldings.Geometry.SegmentSubdivision

/-!
# Distinct subdivided open edges cannot overlap

Consecutive marked intervals on a common line have equal carriers whenever
they intersect. Marked endpoints of every original pairwise intersection
force any intersecting subdivided edges onto a common line, including when
the original segments overlap or coincide.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unmarked_segments_eq_on_line {V : Set E} {p q a b c d x : E} (different : p ≠ q)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (ab : a ≠ b) (cd : c ≠ d)
    (a_line : a ∈ affineSpan ℝ ({p, q} : Set E))
    (b_line : b ∈ affineSpan ℝ ({p, q} : Set E))
    (c_line : c ∈ affineSpan ℝ ({p, q} : Set E))
    (d_line : d ∈ affineSpan ℝ ({p, q} : Set E))
    (first : Disjoint V (openSegment ℝ a b)) (second : Disjoint V (openSegment ℝ c d))
    (hx : x ∈ openSegment ℝ a b) (hy : x ∈ openSegment ℝ c d) :
    segment ℝ a b = segment ℝ c d := by
  let coordinate := lineCoordinate p q
  let line := affineSpan ℝ ({p, q} : Set E)
  let T := coordinate '' (V ∩ (line : Set E))
  have marked {z : E} (hz : z ∈ V) (on_line : z ∈ line) : coordinate z ∈ T :=
    ⟨z, ⟨hz, on_line⟩, rfl⟩
  have preserves_gap {u v : E} (ends : u ≠ v) (u_line : u ∈ line) (v_line : v ∈ line)
      (gap : Disjoint V (openSegment ℝ u v)) :
      Disjoint T (Set.Ioo (min (coordinate u) (coordinate v))
        (max (coordinate u) (coordinate v))) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, ⟨hz, z_line⟩, rfl⟩ between
    have on_segment := (lineCoordinate_mem_openSegment_iff different ends u_line v_line z_line).mpr
      between
    exact Set.disjoint_left.mp gap hz on_segment
  have x_line : x ∈ line := line.convex.segment_subset a_line b_line
    (openSegment_subset_segment ℝ a b hx)
  have first_image := (lineCoordinate_mem_openSegment_iff different ab a_line b_line x_line).mp hx
  have second_image := (lineCoordinate_mem_openSegment_iff different cd c_line d_line x_line).mp hy
  have equal := marked_unordered_gap_unique (marked ha a_line) (marked hb b_line)
    (marked hc c_line) (marked hd d_line) (preserves_gap ab a_line b_line first)
    (preserves_gap cd c_line d_line second) first_image second_image
  ext y
  by_cases on_line : y ∈ line
  · rw [lineCoordinate_mem_segment_iff different a_line b_line on_line,
      lineCoordinate_mem_segment_iff different c_line d_line on_line, equal]
  · constructor
    · intro member
      exact (on_line (line.convex.segment_subset a_line b_line member)).elim
    · intro member
      exact (on_line (line.convex.segment_subset c_line d_line member)).elim

theorem unmarked_segments_eq_of_parent_intersection {V : Set E}
    {a b c d p q r s u v x : E}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (ab : a ≠ b) (cd : c ≠ d)
    (first : Disjoint V (openSegment ℝ a b)) (second : Disjoint V (openSegment ℝ c d))
    (first_parent : segment ℝ a b ⊆ segment ℝ p q)
    (second_parent : segment ℝ c d ⊆ segment ℝ r s)
    (hu : u ∈ V) (_hv : v ∈ V)
    (intersection : segment ℝ p q ∩ segment ℝ r s = segment ℝ u v)
    (hx : x ∈ openSegment ℝ a b) (hy : x ∈ openSegment ℝ c d) :
    segment ℝ a b = segment ℝ c d := by
  have in_intersection : x ∈ segment ℝ p q ∩ segment ℝ r s :=
    ⟨first_parent (openSegment_subset_segment ℝ a b hx),
      second_parent (openSegment_subset_segment ℝ c d hy)⟩
  have different : u ≠ v := by
    intro equal
    have on_segment := (Set.ext_iff.mp intersection x).mp in_intersection
    have same : x = u := by simpa [equal] using on_segment
    exact Set.disjoint_left.mp first (same ▸ hu) hx
  have first_endpoint := (Set.ext_iff.mp intersection u).mpr (left_mem_segment ℝ u v)
  have last_endpoint := (Set.ext_iff.mp intersection v).mpr (right_mem_segment ℝ u v)
  have line_first : affineSpan ℝ ({u, v} : Set E) = affineSpan ℝ ({p, q} : Set E) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (segment_subset_line p q first_endpoint.1)
      (segment_subset_line p q last_endpoint.1) different
  have line_second : affineSpan ℝ ({u, v} : Set E) = affineSpan ℝ ({r, s} : Set E) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (segment_subset_line r s first_endpoint.2)
      (segment_subset_line r s last_endpoint.2) different
  refine unmarked_segments_eq_on_line different ha hb hc hd ab cd ?_ ?_ ?_ ?_
    first second hx hy
  · rw [line_first]
    exact segment_subset_line p q (first_parent (left_mem_segment ℝ a b))
  · rw [line_first]
    exact segment_subset_line p q (first_parent (right_mem_segment ℝ a b))
  · rw [line_second]
    exact segment_subset_line r s (second_parent (left_mem_segment ℝ c d))
  · rw [line_second]
    exact segment_subset_line r s (second_parent (right_mem_segment ℝ c d))

end Unfoldings
