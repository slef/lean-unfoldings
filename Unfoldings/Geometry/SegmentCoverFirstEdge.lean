module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic

/-! A finite segment cover of a chord begins with an edge at its endpoint. -/

@[expose] public section

namespace Unfoldings

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem endpoints_comparable_of_shared_point {x y w z : E}
    (xz : x ≠ z) (in_y : z ∈ openSegment ℝ x y) (in_w : z ∈ segment ℝ x w) :
    w ∈ segment ℝ x y ∨ y ∈ openSegment ℝ x w := by
  obtain ⟨a, ha, ae⟩ := (openSegment_eq_image_lineMap ℝ x y ▸ in_y)
  obtain ⟨b, hb, be⟩ := (segment_eq_image_lineMap ℝ x w ▸ in_w)
  have b_pos : 0 < b := lt_of_le_of_ne hb.1 (fun h => xz (by simpa [← h] using be))
  rw [AffineMap.lineMap_apply_module'] at ae be
  have scale : a • (y - x) = b • (w - x) :=
    add_right_cancel (ae.trans be.symm)
  by_cases ab : a ≤ b
  · left
    rw [segment_eq_image_lineMap]
    refine ⟨a / b, ⟨div_nonneg ha.1.le b_pos.le, (div_le_one b_pos).mpr ab⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', div_eq_inv_mul, mul_smul, scale, ← mul_smul,
      inv_mul_cancel₀ b_pos.ne', one_smul, sub_add_cancel]
  · right
    rw [openSegment_eq_image_lineMap]
    refine ⟨b / a, ⟨div_pos b_pos ha.1, (div_lt_one ha.1).mpr (lt_of_not_ge ab)⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', div_eq_inv_mul, mul_smul, ← scale, ← mul_smul,
      inv_mul_cancel₀ ha.1.ne', one_smul, sub_add_cancel]

/-- If a finite family of segments covers a nontrivial chord and both chord
endpoints avoid the open edges, an edge starting at the first endpoint lies
inside the chord. -/
theorem exists_first_edge_of_finite_segment_cover
    {I : Type*} [Finite I] (left right : I → E) {x y : E} (different : x ≠ y)
    (cover : segment ℝ x y ⊆ ⋃ i, segment ℝ (left i) (right i))
    (at_x : ∀ i, x ∉ openSegment ℝ (left i) (right i))
    (at_y : ∀ i, y ∉ openSegment ℝ (left i) (right i)) :
    ∃ i, (left i = x ∧ right i ∈ segment ℝ x y ∧ right i ≠ x) ∨
      (right i = x ∧ left i ∈ segment ℝ x y ∧ left i ≠ x) := by
  let A (i : I) := openSegment ℝ x y ∩ segment ℝ (left i) (right i)
  have included : openSegment ℝ x y ⊆ ⋃ i, A i := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (cover (openSegment_subset_segment ℝ _ _ hz))
    exact mem_iUnion.mpr ⟨i, hz, hi⟩
  have near : x ∈ closure (⋃ i, A i) :=
    closure_mono included (segment_subset_closure_openSegment (left_mem_segment ℝ x y))
  rw [closure_iUnion_of_finite] at near
  obtain ⟨i, hx⟩ := mem_iUnion.mp near
  have edge : x ∈ segment ℝ (left i) (right i) :=
    closure_minimal inter_subset_right (by
      rw [segment_eq_image_lineMap]
      have cont : Continuous (AffineMap.lineMap (left i) (right i) : ℝ → E) := by
        change Continuous (fun t : ℝ => AffineMap.lineMap (left i) (right i) t)
        simp only [AffineMap.lineMap_apply_module']
        exact (continuous_id.smul continuous_const).add continuous_const
      exact (isCompact_Icc.image cont).isClosed) hx
  have nonempty : (A i).Nonempty := by
    by_contra h
    have empty := not_nonempty_iff_eq_empty.mp h
    rw [empty, closure_empty] at hx
    exact hx
  obtain ⟨z, hz, hz'⟩ := nonempty
  have xz : x ≠ z := fun h => different (by
    have h' := h.symm ▸ hz
    exact left_mem_openSegment_iff.mp h')
  have extend_edge {w : E} (contains : z ∈ segment ℝ x w)
      (endpoint : y ∉ openSegment ℝ x w) : w ∈ segment ℝ x y ∧ w ≠ x := by
    refine ⟨(endpoints_comparable_of_shared_point xz hz contains).resolve_right endpoint, ?_⟩
    intro eq
    rw [eq, segment_same, mem_singleton_iff] at contains
    exact xz contains.symm
  by_cases l : left i = x
  · refine ⟨i, Or.inl ⟨l, ?_⟩⟩
    rw [l] at hz'
    apply extend_edge hz'
    simpa only [l] using at_y i
  · have r : right i = x := by
      by_contra different_r
      exact at_x i (mem_openSegment_of_ne_left_right l different_r edge)
    refine ⟨i, Or.inr ⟨r, ?_⟩⟩
    rw [r, segment_symm] at hz'
    apply extend_edge hz'
    simpa only [r, openSegment_symm] using at_y i

end Unfoldings
