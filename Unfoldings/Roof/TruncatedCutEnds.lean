module

public import Unfoldings.Roof.TruncatedBoundaryRoots

/-! Every nonterminal point of the actual finite cut lies strictly below its truncation level. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

/-- The actual cut has no hidden level points between its original terminal endpoints. -/
theorem truncatedCarrier_strict_or_terminalPoint {p : Plane}
    (member : p ∈ R.truncatedCarrier level higher) :
    G.height p < level ∨ ∃ r : {v // v ∈ R.parents.roots}, p = R.terminalPoint level r := by
  obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp member
  obtain ⟨t, bounds, at_point⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_edge
  by_cases first : t = 0
  · have same : p = K.projectedVertex v := by
      simpa only [first, AffineMap.lineMap_apply_zero, truncatedPoint] using at_point.symm
    exact Or.inl (same ▸ higher v)
  by_cases last : t = 1
  · have same : p = R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v)) := by
      simpa only [last, AffineMap.lineMap_apply_one] using at_point.symm
    cases parent : (R.truncatedParents level higher).parent (.inl v) with
    | inl w =>
      rw [parent] at same
      exact Or.inl (same ▸ higher w)
    | inr r =>
      rw [parent] at same
      exact Or.inr ⟨r, same⟩
  · left
    apply R.truncated_segment_height_lt level higher v
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨lt_of_le_of_ne bounds.1 (Ne.symm first), lt_of_le_of_ne bounds.2 last⟩, at_point⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
