module

public import Unfoldings.Geometry.TriangleFanBoundary
public import Unfoldings.Geometry.ConvexSegmentExit

/-! A proper affine supporting line meets a triangle only in its actual edges and vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- An affine function of one sign on a triangle vanishes on a whole edge if it
vanishes at a nonvertex point of that edge. -/
theorem affine_zero_on_edge_of_nonnegative (T : Triangle) (height : Plane →ᵃ[ℝ] ℝ)
    (nonnegative : ∀ x ∈ T.carrier, 0 ≤ height x) (e : Fin 3) (x : T.Edge e)
    (regular : ¬ T.IsVertex x) (zero : height x.val = 0) :
    ∀ p ∈ T.edge e, height p = 0 := by
  have ends := T.edge_vertex_iff e x
  have first_ne : x.val ≠ T.vertex e := fun equal => regular (ends.mpr (Or.inl equal))
  have last_ne : x.val ≠ T.vertex (next e) := fun equal => regular (ends.mpr (Or.inr equal))
  have open_edge := mem_openSegment_of_ne_left_right first_ne.symm last_ne.symm x.property
  obtain ⟨t, bounds, expression⟩ := (openSegment_eq_image_lineMap ℝ _ _).subset open_edge
  have formula := congrArg height expression
  rw [height.apply_lineMap, AffineMap.lineMap_apply_ring, zero] at formula
  have first_nonnegative := nonnegative (T.vertex e) (T.vertex_mem e)
  have last_nonnegative := nonnegative (T.vertex (next e)) (T.vertex_mem (next e))
  have first_zero : height (T.vertex e) = 0 := by
    have other := mul_nonneg bounds.1.le last_nonnegative
    have product : (1 - t) * height (T.vertex e) = 0 :=
      le_antisymm (by linarith) (mul_nonneg (sub_pos.mpr bounds.2).le first_nonnegative)
    exact (mul_eq_zero.mp product).resolve_left (sub_pos.mpr bounds.2).ne'
  have last_zero : height (T.vertex (next e)) = 0 := by
    rw [first_zero, mul_zero, zero_add] at formula
    exact (mul_eq_zero.mp formula).resolve_left bounds.1.ne'
  have convex_zero : Convex ℝ {p | height p = 0} :=
    (convex_singleton (0 : ℝ)).affine_preimage height
  exact fun p member => convex_zero.segment_subset first_zero last_zero member

/-- A nonvertex contact with a supporting line belongs to an entire triangle edge on that line. -/
theorem exists_zero_edge_of_nonvertex (T : Triangle) (height : Plane →ᵃ[ℝ] ℝ)
    (proper : height ≠ 0) (nonnegative : ∀ x ∈ T.carrier, 0 ≤ height x)
    {x : Plane} (member : x ∈ T.carrier) (regular : ¬ T.IsVertex x)
    (zero : height x = 0) : ∃ e : Fin 3, x ∈ T.edge e ∧ ∀ p ∈ T.edge e, height p = 0 := by
  have positive_corner : ∃ i, 0 < height (T.vertex i) := by
    by_contra absent
    apply proper
    apply T.affine_ext
    intro i
    exact le_antisymm (not_lt.mp (fun positive => absent ⟨i, positive⟩))
      (nonnegative _ (T.vertex_mem i))
  obtain ⟨i, positive⟩ := positive_corner
  have frontier : x ∈ frontier T.carrier := by
    refine ⟨subset_closure member, fun inside => ?_⟩
    obtain ⟨t, after, extended⟩ := exists_lineMap_beyond_one_mem (q := T.vertex i) inside
    have lower := nonnegative _ extended
    rw [height.apply_lineMap, AffineMap.lineMap_apply_ring, zero, mul_zero, add_zero] at lower
    exact (not_lt_of_ge lower) (mul_neg_of_neg_of_pos (sub_neg.mpr after) positive)
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (T.frontier_eq_union_edges ▸ frontier)
  exact ⟨e, on_edge, T.affine_zero_on_edge_of_nonnegative height nonnegative e
    ⟨x, on_edge⟩ regular zero⟩

end Unfoldings.Triangle
