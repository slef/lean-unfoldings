module

public import Unfoldings.Geometry.SegmentCoverFirstEdge
public import Mathlib.Tactic.Module

/-! A directed segment covered by subedges retains a forward edge at every mesh vertex. -/

@[expose] public section

namespace Unfoldings

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

private theorem right_not_mem_open_subsegment {a b x y : E} (different : a ≠ b)
    (x_in : x ∈ segment ℝ a b) (y_in : y ∈ segment ℝ a b) (xy : x ≠ y) :
    b ∉ openSegment ℝ x y := by
  intro inside
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b
  obtain ⟨u, u_in, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset x_in
  obtain ⟨v, v_in, at_y⟩ := (segment_eq_image_lineMap ℝ a b).subset y_in
  have unequal : u ≠ v := fun equal => xy (at_x.symm.trans (equal ▸ at_y))
  have lifted : b ∈ L '' openSegment ℝ u v := by
    rw [image_openSegment]
    change b ∈ openSegment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v)
    rwa [at_x, at_y]
  obtain ⟨s, s_in, at_b⟩ := lifted
  have last : s = 1 := (AffineMap.lineMap_injective ℝ different)
    (at_b.trans (AffineMap.lineMap_apply_one a b).symm)
  rw [last, openSegment_eq_Ioo' unequal] at s_in
  exact (not_lt_of_ge (max_le u_in.2 v_in.2)) s_in.2

/-- Every nonterminal point of a coarse segment that is already a mesh vertex
has a fine edge oriented forward along the same segment. -/
theorem exists_forward_edge_of_finite_subsegment_cover
    (left right : I → E) {a b p : E} (different : a ≠ b)
    (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (left i) (right i))
    (left_in : ∀ i, left i ∈ segment ℝ a b)
    (right_in : ∀ i, right i ∈ segment ℝ a b)
    (genuine : ∀ i, left i ≠ right i)
    (at_vertex : ∀ i, p ∉ openSegment ℝ (left i) (right i))
    (on_path : p ∈ segment ℝ a b) (nonterminal : p ≠ b) :
    ∃ i, (left i = p ∧ right i ∈ segment ℝ p b ∧ right i ≠ p) ∨
      (right i = p ∧ left i ∈ segment ℝ p b ∧ left i ≠ p) :=
  exists_first_edge_of_finite_segment_cover left right nonterminal
    (((convex_segment a b).segment_subset on_path (right_mem_segment ℝ a b)).trans cover)
    at_vertex (fun i => right_not_mem_open_subsegment different (left_in i) (right_in i) (genuine i))

/-- Going forward from an interior point along the rest of a coarse edge
preserves the heading, up to positive scaling. -/
theorem exists_pos_smul_of_forward_segment {a b p q : E}
    (start : p ∈ segment ℝ a b) (nonterminal : p ≠ b)
    (finish : q ∈ segment ℝ p b) (different : q ≠ p) :
    ∃ s : ℝ, 0 < s ∧ q - p = s • (b - a) := by
  obtain ⟨u, hu, at_p⟩ := (segment_eq_image_lineMap ℝ a b).subset start
  obtain ⟨v, hv, at_q⟩ := (segment_eq_image_lineMap ℝ p b).subset finish
  have before : u < 1 := lt_of_le_of_ne hu.2 (fun equal =>
    nonterminal (at_p.symm.trans (equal ▸ AffineMap.lineMap_apply_one a b)))
  have after : 0 < v := lt_of_le_of_ne hv.1 (fun equal =>
    different (at_q.symm.trans (equal ▸ AffineMap.lineMap_apply_zero p b)))
  refine ⟨v * (1 - u), mul_pos after (sub_pos.mpr before), ?_⟩
  rw [← at_q, AffineMap.lineMap_apply_module', add_sub_cancel_right]
  have remains : b - p = (1 - u) • (b - a) := by
    rw [← at_p, AffineMap.lineMap_apply_module']
    module
  rw [remains, smul_smul]

end Unfoldings
