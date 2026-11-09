module

public import Mathlib.Analysis.Convex.Topology

/-!
# Straight chords through convex boundary points

If an interior point of a segment in a convex set is on the frontier, the
entire segment is on the frontier. Otherwise a point of the segment in the
ambient interior would force every interior segment point into the interior.
-/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]

theorem segment_subset_frontier_of_openSegment_mem {s : Set E} (convex : Convex ℝ s)
    {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (between : z ∈ openSegment ℝ x y)
    (boundary : z ∈ frontier s) : segment ℝ x y ⊆ frontier s := by
  intro w hw
  refine ⟨subset_closure (convex.segment_subset hx hy hw), ?_⟩
  intro inside
  have line : w ∈ Set.range (AffineMap.lineMap x y : ℝ → E) := by
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨t, _, rfl⟩ := hw
    exact ⟨t, rfl⟩
  rcases openSegment_subset_union x y line between with same | first | last
  · exact boundary.2 (same.symm ▸ inside)
  · exact boundary.2 (convex.openSegment_self_interior_subset_interior hx inside first)
  · exact boundary.2 (convex.openSegment_interior_self_subset_interior inside hy last)

end Unfoldings
