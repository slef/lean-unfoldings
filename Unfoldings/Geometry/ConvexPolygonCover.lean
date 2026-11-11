module

public import Unfoldings.Geometry.ConvexPolygonFan

/-!
# Finite genuine triangle covers of compact convex polygons

A finite boundary-segment cover gives a finite center-triangle cover. Singleton
rim cells cause no gap: first prove coverage away from finitely many radial
lines, then use closedness of the finite triangle union to recover every point.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {S : Set Plane} (compact : IsCompact S) (convex : Convex ℝ S)
  {q : Plane} (inside : q ∈ interior S)
  {ι : Type*} [Finite ι] [Nonempty ι] (first last : ι → Plane)
  (boundary : ∀ i, segment ℝ (first i) (last i) ⊆ frontier S)
  (covers : ∀ p ∈ frontier S, ∃ i, p ∈ segment ℝ (first i) (last i))

def polygonFanTriangle (i : {i : ι // first i ≠ last i}) : Triangle :=
  convexBoundaryTriangle compact convex inside i.property (boundary i.val)

omit [Finite ι] [Nonempty ι] in
theorem polygonFanTriangle_subset (i : {i : ι // first i ≠ last i}) :
    (polygonFanTriangle compact convex inside first last boundary i).carrier ⊆ S :=
  convexBoundaryTriangle_subset compact convex inside i.property (boundary i.val)

include covers in
/-- Degenerate rim segments can be discarded without losing any part of the convex body. -/
theorem polygonFanTriangle_cover :
    S = ⋃ i : {i : ι // first i ≠ last i},
      (polygonFanTriangle compact convex inside first last boundary i).carrier := by
  classical
  let := Fintype.ofFinite ι
  let union := ⋃ i : {i : ι // first i ≠ last i},
    (polygonFanTriangle compact convex inside first last boundary i).carrier
  have closed_union : IsClosed union := isClosed_iUnion_of_finite
    (fun i =>
      (polygonFanTriangle compact convex inside first last boundary i).compact_carrier.isClosed)
  have different (i : ι) : q ≠ first i := by
    intro equal
    exact (boundary i (left_mem_segment ℝ _ _)).2 (equal ▸ inside)
  let regular := {x : Plane | ∀ i, orient q (first i) x ≠ 0}
  have dense : Dense regular := by
    simpa only [regular, orientMap_apply] using
      AffineArrangement.dense_regular (fun i => orientMap q (first i))
        (fun i => orientMap_ne_zero (different i))
  have regular_cover : interior S ∩ regular ⊆ union := by
    rintro x ⟨member, avoids⟩
    have x_ne : x ≠ q := by
      intro equal
      have nonzero := avoids (Classical.arbitrary ι)
      rw [equal, orient_self_left] at nonzero
      exact nonzero rfl
    obtain ⟨a, positive, on_frontier⟩ := exists_frontier_on_positive_ray compact convex inside x_ne
    obtain ⟨i, on_edge⟩ := covers _ on_frontier
    have genuine : first i ≠ last i := by
      intro same
      rw [same, segment_same, Set.mem_singleton_iff] at on_edge
      have collinear : orient q (first i) x = 0 := by
        have at_ray := congrArg (orient q (first i)) on_edge
        have formula : orient q (first i) (q + a • (x - q)) = a * orient q (first i) x := by
          simp only [orient, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          ring
        rw [formula, ← same, orient_self_right] at at_ray
        exact (mul_eq_zero.mp at_ray).resolve_left positive.ne'
      exact avoids i collinear
    let triangle := polygonFanTriangle compact convex inside first last boundary ⟨i, genuine⟩
    have q_member : q ∈ triangle.carrier := triangle.vertex_mem 0
    have edge_member : q + a • (x - q) ∈ triangle.carrier := by
      exact triangle.convex_carrier.segment_subset (triangle.vertex_mem 1) (triangle.vertex_mem 2)
        on_edge
    have factor := one_le_frontier_ray_factor convex inside (interior_subset member) positive
      on_frontier
    have inverse : a⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨inv_nonneg.mpr positive.le, (inv_le_one₀ positive).mpr factor⟩
    have point := triangle.convex_carrier.lineMap_mem q_member edge_member inverse
    have recovered : AffineMap.lineMap q (q + a • (x - q)) a⁻¹ = x := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ positive.ne', one_smul, sub_add_cancel]
    rw [recovered] at point
    exact Set.mem_iUnion.mpr ⟨⟨i, genuine⟩, point⟩
  have inside_union : interior S ⊆ union :=
    (dense.open_subset_closure_inter isOpen_interior).trans
      ((closure_mono regular_cover).trans closed_union.closure_eq.subset)
  have original_subset : S ⊆ union := by
    have closure := convex.closure_interior_eq_closure_of_nonempty_interior ⟨q, inside⟩
    rw [compact.isClosed.closure_eq] at closure
    rw [← closure]
    exact (closure_mono inside_union).trans closed_union.closure_eq.subset
  exact Set.Subset.antisymm original_subset (Set.iUnion_subset (fun i =>
    polygonFanTriangle_subset compact convex inside first last boundary i))

end Unfoldings
