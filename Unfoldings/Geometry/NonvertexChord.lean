module

public import Unfoldings.Geometry.Edge
public import Mathlib.Analysis.Convex.Extreme

/-! A nonvertex point of a closed triangle lies strictly inside a genuine chord. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem exists_open_chord_of_nonvertex (T : Triangle) {p : Plane} (member : p ∈ T.carrier)
    (regular : ¬ T.IsVertex p) :
    ∃ a ∈ T.carrier, ∃ b ∈ T.carrier, a ≠ b ∧ p ∈ openSegment ℝ a b := by
  classical
  have not_extreme : p ∉ T.carrier.extremePoints ℝ :=
    fun extreme => regular (extremePoints_convexHull_subset extreme)
  have absent : ¬ ∀ a ∈ T.carrier, ∀ b ∈ T.carrier,
      p ∈ openSegment ℝ a b → a = p := fun all => not_extreme ⟨member, all⟩
  push Not at absent
  obtain ⟨a, ha, b, hb, between, different⟩ := absent
  refine ⟨a, ha, b, hb, ?_, between⟩
  intro equal
  have at_a : p = a := by
    simpa only [← equal, openSegment_same, Set.mem_singleton_iff] using between
  exact different at_a.symm

end Unfoldings.Triangle
