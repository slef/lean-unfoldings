module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Affine

/-! A segment from an interior point to an exterior point crosses a convex compact frontier. -/

@[expose] public section

namespace Unfoldings

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A segment ending at an interior point extends slightly beyond that endpoint in the set. -/
theorem exists_lineMap_beyond_one_mem {S : Set E} {q p : E} (inside : p ∈ interior S) :
    ∃ t : ℝ, 1 < t ∧ AffineMap.lineMap q p t ∈ S := by
  have near : Filter.Tendsto (AffineMap.lineMap q p) (𝓝 (1 : ℝ)) (𝓝 p) := by
    simpa only [AffineMap.lineMap_apply_one] using
      (AffineMap.lineMap_continuous (p := q) (q := p)).tendsto (1 : ℝ)
  have members : ∀ᶠ t in 𝓝[>] (1 : ℝ), AffineMap.lineMap q p t ∈ S :=
    (near.mono_left nhdsWithin_le_nhds) (mem_interior_iff_mem_nhds.mp inside)
  have greater : ∀ᶠ t in 𝓝[>] (1 : ℝ), 1 < t := self_mem_nhdsWithin
  obtain ⟨t, member, after⟩ := (members.and greater).exists
  exact ⟨t, after, member⟩

/-- The crossing lies strictly between the endpoints of the original straight segment. -/
theorem exists_frontier_on_segment {S : Set E} (compact : IsCompact S) (convex : Convex ℝ S)
    {q p : E} (inside : q ∈ interior S) (outside : p ∉ S) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, AffineMap.lineMap q p t ∈ frontier S := by
  obtain ⟨h, interior_image, closed_image, frontier_image⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex ⟨q, inside⟩
      compact.isBounded
  let height (t : ℝ) := ‖h (AffineMap.lineMap q p t)‖
  have first : height 0 < 1 := by
    have member : h q ∈ Metric.ball (0 : E) 1 := interior_image ▸ ⟨q, inside, rfl⟩
    simpa only [height, AffineMap.lineMap_apply_zero, Metric.mem_ball, dist_zero_right] using member
  have last : 1 < height 1 := by
    by_contra below
    have member : h p ∈ Metric.closedBall (0 : E) 1 := by
      simpa only [height, AffineMap.lineMap_apply_one, Metric.mem_closedBall, dist_zero_right]
        using le_of_not_gt below
    rw [← closed_image] at member
    obtain ⟨r, in_closure, same⟩ := member
    have same : r = p := h.injective same
    exact outside (same ▸ (compact.isClosed.closure_eq ▸ in_closure))
  have continuous : Continuous height :=
    (h.continuous.comp AffineMap.lineMap_continuous).norm
  obtain ⟨t, bounds, at_boundary⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 from zero_le_one) continuous.continuousOn
      ⟨first.le, last.le⟩
  have positive : 0 < t := by
    by_contra nonpositive
    have zero : t = 0 := le_antisymm (le_of_not_gt nonpositive) bounds.1
    rw [zero] at at_boundary
    linarith
  have less : t < 1 := by
    by_contra not_less
    have one : t = 1 := le_antisymm bounds.2 (le_of_not_gt not_less)
    rw [one] at at_boundary
    linarith
  refine ⟨t, ⟨positive, less⟩, ?_⟩
  have member : h (AffineMap.lineMap q p t) ∈ h '' frontier S := by
    rw [frontier_image]
    simpa only [Metric.mem_sphere, dist_zero_right] using at_boundary
  obtain ⟨r, boundary, same⟩ := member
  exact h.injective same ▸ boundary

end Unfoldings
