module

public import Unfoldings.Geometry.QuadrantCircle
public import Unfoldings.Topology.IntervalFrontier

/-! Two possible bank values force one angular interval on every circle inside a source quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem quadrantCirclePoint_image_preimage {U : Set ℂ} (center : ℂ) {radius : ℝ}
    (positive : 0 < radius)
    (quadrant : ∀ z ∈ U, 0 < (z - center).re ∧ 0 < (z - center).im) :
    quadrantCirclePoint center radius '' (quadrantCirclePoint center radius ⁻¹' U) =
      U ∩ {z | ‖z - center‖ = radius} := by
  have inside := quadrantCirclePoint_preimage_subset center positive quadrant
  ext z
  constructor
  · rintro ⟨x, member, rfl⟩
    exact ⟨member, norm_quadrantCirclePoint_sub center positive.le
      ⟨(inside member).1.le, (inside member).2.le⟩⟩
  · rintro ⟨member, size⟩
    have value := quadrantCirclePoint_eq_of_norm center
      ⟨(quadrant z member).1.le, (quadrant z member).2.le⟩ size
    refine ⟨(z - center).re, ?_, value⟩
    change quadrantCirclePoint center radius (z - center).re ∈ U
    rwa [value]

/-- Within one source quadrant, no additional angular component can hide between
the two possible bank values. The empty-circle case is retained explicitly. -/
theorem quadrant_circle_preimage_interval {U : Set ℂ} (opened : IsOpen U) (center : ℂ)
    {radius : ℝ} (positive : 0 < radius)
    (quadrant : ∀ z ∈ U, 0 < (z - center).re ∧ 0 < (z - center).im)
    (left right : ℂ)
    (boundary_values : ∀ z ∈ frontier U, ‖z - center‖ = radius → z = left ∨ z = right) :
    quadrantCirclePoint center radius ⁻¹' U = ∅ ∨
      quadrantCirclePoint center radius ⁻¹' U =
        Set.Ioo (min (left - center).re (right - center).re)
          (max (left - center).re (right - center).re) := by
  let γ := quadrantCirclePoint center radius
  let V := γ ⁻¹' U
  have continuous : Continuous γ := continuous_quadrantCirclePoint center radius
  have open_V : IsOpen V := opened.preimage continuous
  have inside : V ⊆ Set.Ioo 0 radius := quadrantCirclePoint_preimage_subset center positive quadrant
  have closure_inside : closure V ⊆ Set.Icc 0 radius := closure_minimal
    (fun _ member => ⟨(inside member).1.le, (inside member).2.le⟩) isClosed_Icc
  have below : BddBelow V := ⟨0, fun _ member => (inside member).1.le⟩
  have above : BddAbove V := ⟨radius, fun _ member => (inside member).2.le⟩
  have frontier_values : frontier V ⊆ {(left - center).re, (right - center).re} := by
    intro x member
    have physical := continuous.frontier_preimage_subset U member
    have size := norm_quadrantCirclePoint_sub center positive.le (closure_inside member.1)
    rcases boundary_values (γ x) physical size with first | last
    · have coordinate := congrArg (fun z : ℂ => (z - center).re) first
      rw [quadrantCirclePoint_re] at coordinate
      exact Or.inl coordinate
    · have coordinate := congrArg (fun z : ℂ => (z - center).re) last
      rw [quadrantCirclePoint_re] at coordinate
      exact Or.inr (Set.mem_singleton_iff.mpr coordinate)
  rcases Set.eq_empty_or_nonempty V with empty | nonempty
  · exact Or.inl empty
  · right
    by_cases ordered : (left - center).re ≤ (right - center).re
    · rw [min_eq_left ordered, max_eq_right ordered]
      exact (isOpen_bounded_eq_Ioo_of_frontier_subset open_V below above nonempty ordered
        frontier_values).2
    · have reverse := le_of_not_ge ordered
      rw [min_eq_right reverse, max_eq_left reverse]
      have swapped : frontier V ⊆ {(right - center).re, (left - center).re} := by
        intro x member
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using frontier_values member
      exact (isOpen_bounded_eq_Ioo_of_frontier_subset open_V below above nonempty reverse swapped).2

end Unfoldings
