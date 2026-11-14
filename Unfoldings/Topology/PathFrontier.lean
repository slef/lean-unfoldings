module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.UnitInterval

/-! Paths from the interior of a closed set to its exterior cross its frontier at an inner time. -/

@[expose] public section

namespace Unfoldings

/-- Boundary crossing occurs strictly between the endpoints. No local regularity or convexity
of the closed set is required. -/
theorem exists_inner_time_mem_frontier {X : Type*} [TopologicalSpace X]
    {s : Set X} (closed : IsClosed s) (path : unitInterval → X) (continuous : Continuous path)
    (first : path 0 ∈ interior s) (last : path 1 ∉ s) :
    ∃ t : unitInterval, (0 : ℝ) < t ∧ (t : ℝ) < 1 ∧ path t ∈ frontier s := by
  have nonempty : (path ⁻¹' s).Nonempty := ⟨0, show path 0 ∈ s from interior_subset first⟩
  have proper : path ⁻¹' s ≠ Set.univ := by
    intro equal
    apply last
    have member : (1 : unitInterval) ∈ path ⁻¹' s := by
      rw [equal]
      exact Set.mem_univ _
    exact member
  obtain ⟨t, boundary⟩ := nonempty_frontier_iff.mpr ⟨nonempty, proper⟩
  have physical := continuous.frontier_preimage_subset s boundary
  have positive : (0 : ℝ) < t := by
    by_contra not_positive
    have zero : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt not_positive) t.property.1)
    rw [zero] at physical
    exact physical.2 first
  have before : (t : ℝ) < 1 := by
    by_contra not_before
    have one : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt not_before))
    rw [one] at physical
    exact last (closed.frontier_subset physical)
  exact ⟨t, positive, before, physical⟩

end Unfoldings
