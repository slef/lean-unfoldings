module

public import Unfoldings.Geometry.AdjacentBoundaryEdges
public import Unfoldings.Geometry.CornerSpan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# An interior center splits a simple convex boundary corner angle

For a nonstraight corner, supporting half-planes put the center in the
positive span of the two incident rays. Straight subdivisions use the
supplementary-angle identity. Thus center triangulation gives exact angle
addition even when consecutive polygon vertices are collinear.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped NNReal

theorem coord_opposite_nonneg_of_boundary_edge {s : Set Plane}
    (convex : Convex ℝ s) (closed : IsClosed s) {x : Plane}
    (inside : x ∈ interior s) (T : Triangle) (e : Fin 3)
    (edge : T.edge e ⊆ frontier s) (opposite : T.opposite e ∈ s) :
    0 ≤ T.coord (Triangle.next (Triangle.next e)) x := by
  have side := orient_mul_nonneg_of_boundary_segment convex closed inside
    (T.edge_endpoints_ne e) edge opposite
  rw [T.orient_eq_coord_mul e x] at side
  have scaled : 0 ≤ (orient (T.vertex e) (T.vertex (Triangle.next e)) (T.opposite e)) ^ 2 *
      T.coord (Triangle.next (Triangle.next e)) x := by
    convert side using 1
    ring
  have positive := sq_pos_of_ne_zero (T.orient_edge_ne_zero e)
  by_contra negative
  exact not_le_of_gt (mul_neg_of_pos_of_neg positive (lt_of_not_ge negative)) scaled

theorem angle_eq_add_of_adjacent_boundary_edges {s : Set Plane}
    (convex : Convex ℝ s) (closed : IsClosed s) {a b c x : Plane}
    (inside : x ∈ interior s) (ab : a ≠ b) (bc : b ≠ c)
    (first : segment ℝ a b ⊆ frontier s) (second : segment ℝ b c ⊆ frontier s)
    (left : Disjoint (openSegment ℝ a b) (segment ℝ b c))
    (right : Disjoint (openSegment ℝ b c) (segment ℝ a b)) :
    EuclideanGeometry.angle a b c =
      EuclideanGeometry.angle a b x + EuclideanGeometry.angle x b c := by
  by_cases straight : orient a b c = 0
  · have between := wbtw_of_collinear_disjoint_edges
      ((orient_eq_zero_iff_collinear a b c).mp straight) left right
    have angle : EuclideanGeometry.angle a b c = Real.pi :=
      EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr ⟨between, ab.symm, bc⟩
    have sum := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi x angle
    rw [EuclideanGeometry.angle_comm x b a] at sum
    linarith
  · let T : Triangle := ⟨![b, c, a], by change orient b c a ≠ 0; rwa [orient_cyclic]⟩
    have ha : a ∈ s := closed.closure_eq ▸ (first (left_mem_segment ℝ _ _)).1
    have hc : c ∈ s := closed.closure_eq ▸ (second (right_mem_segment ℝ _ _)).1
    have next_nonneg : 0 ≤ T.coord 1 x :=
      coord_opposite_nonneg_of_boundary_edge convex closed inside T 2 first hc
    have prev_nonneg : 0 ≤ T.coord 2 x :=
      coord_opposite_nonneg_of_boundary_edge convex closed inside T 0 second ha
    obtain ⟨r, hr, t, ht, equal⟩ :=
      (T.mem_cornerWedge_iff_cornerCombination 0 x).mp ⟨next_nonneg, prev_nonneg⟩
    have vector : t • (a - b) + r • (c - b) = x - b := by
      change r • (c - b) + t • (a - b) + b = x at equal
      rw [add_comm]
      exact (eq_sub_iff_add_eq).mpr equal
    have different : x ≠ b := by
      intro equal
      exact (first (right_mem_segment ℝ a b)).2 (equal ▸ inside)
    change InnerProductGeometry.angle (a - b) (c - b) =
      InnerProductGeometry.angle (a - b) (x - b) + InnerProductGeometry.angle (x - b) (c - b)
    apply (InnerProductGeometry.angle_eq_angle_add_angle_iff (sub_ne_zero.mpr different)).mpr
    right
    rw [Submodule.mem_span_pair]
    exact ⟨⟨t, ht⟩, ⟨r, hr⟩, vector⟩

end Unfoldings
