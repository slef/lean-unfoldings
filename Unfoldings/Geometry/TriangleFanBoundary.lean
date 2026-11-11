module

public import Unfoldings.Geometry.ConvexPolygonFan
public import Unfoldings.Geometry.TriangleFrontier

/-! Boundary intersections of genuine center triangles in an original triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Evaluate any affine function by the triangle's actual barycentric coordinates. -/
theorem affine_apply_eq_sum_coord (T : Triangle) (height : Plane →ᵃ[ℝ] ℝ) (p : Plane) :
    height p = ∑ i : Fin 3, height (T.vertex i) * T.coord i p := by
  have equal : height = ∑ i : Fin 3, height (T.vertex i) • T.coord i := by
    apply T.affine_ext
    intro j
    simp only [Fin.sum_univ_three, AffineMap.coe_add, Pi.add_apply, AffineMap.coe_smul,
      Pi.smul_apply, smul_eq_mul, T.coord_vertex]
    fin_cases j <;> simp
  have applied := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A p) equal
  simpa only [Fin.sum_univ_three, AffineMap.coe_add, Pi.add_apply, AffineMap.coe_smul,
    Pi.smul_apply, smul_eq_mul] using applied

/-- A whole straight segment on a triangle frontier lies in one of its three original edges. -/
theorem boundary_segment_subset_edge (T : Triangle) {a b : Plane}
    (boundary : segment ℝ a b ⊆ frontier T.carrier) : ∃ e, segment ℝ a b ⊆ T.edge e := by
  have mid := boundary (midpoint_mem_segment a b)
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (T.frontier_eq_union_edges ▸ mid)
  have first := T.compact_carrier.isClosed.frontier_subset (boundary (left_mem_segment ℝ a b))
  have last := T.compact_carrier.isClosed.frontier_subset (boundary (right_mem_segment ℝ a b))
  have first_nonnegative := T.carrier_eq_nonneg_coord.le first (next (next e))
  have last_nonnegative := T.carrier_eq_nonneg_coord.le last (next (next e))
  have average := (T.coord (next (next e))).map_midpoint a b
  rw [T.coord_edge_eq_zero e ⟨_, on_edge⟩, midpoint_eq_smul_add] at average
  simp only [smul_eq_mul, invOf_eq_inv] at average
  have first_zero : T.coord (next (next e)) a = 0 := by linarith
  have last_zero : T.coord (next (next e)) b = 0 := by linarith
  exact ⟨e, (convex_segment (𝕜 := ℝ) _ _).segment_subset
    ((T.mem_edge_iff e a).mpr ⟨first, first_zero⟩)
    ((T.mem_edge_iff e b).mpr ⟨last, last_zero⟩)⟩

/-- A center triangle can meet its parent's frontier only along its whole base edge. -/
theorem fan_frontier_subset_base (T : Triangle) {q a b : Plane}
    (inside : q ∈ interior T.carrier) (different : a ≠ b)
    (boundary : segment ℝ a b ⊆ frontier T.carrier) :
    (convexBoundaryTriangle T.compact_carrier T.convex_carrier inside different boundary).carrier ∩
      frontier T.carrier ⊆ segment ℝ a b := by
  intro p member
  let U := convexBoundaryTriangle T.compact_carrier T.convex_carrier inside different boundary
  have u_inside : p ∈ U.carrier := member.1
  have coordinates := U.carrier_eq_nonneg_coord.le u_inside
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (T.frontier_eq_union_edges ▸ member.2)
  let height := T.coord (next (next e))
  have zero : height p = 0 := T.coord_edge_eq_zero e ⟨p, on_edge⟩
  have center : 0 < height (U.vertex 0) := T.interior_eq_pos_coord.le inside _
  have a_nonnegative : 0 ≤ height (U.vertex 1) := T.carrier_eq_nonneg_coord.le
    (T.compact_carrier.isClosed.frontier_subset (boundary (left_mem_segment ℝ a b))) _
  have b_nonnegative : 0 ≤ height (U.vertex 2) := T.carrier_eq_nonneg_coord.le
    (T.compact_carrier.isClosed.frontier_subset (boundary (right_mem_segment ℝ a b))) _
  have weighted := U.affine_apply_eq_sum_coord height p
  rw [Fin.sum_univ_three, zero] at weighted
  have weight_zero : U.coord 0 p = 0 := by
    have first := mul_nonneg a_nonnegative (coordinates 1)
    have last := mul_nonneg b_nonnegative (coordinates 2)
    by_contra nonzero
    have positive := mul_pos center (lt_of_le_of_ne (coordinates 0) (Ne.symm nonzero))
    linarith
  have on_base := (U.mem_edge_iff 1 p).mpr ⟨u_inside, weight_zero⟩
  exact on_base

end Unfoldings.Triangle
