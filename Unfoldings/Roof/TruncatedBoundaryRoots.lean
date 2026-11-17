module

public import Unfoldings.Roof.TruncatedCutSegments
public import Unfoldings.Roof.TruncatedCutEmbedding

/-! The actual bounded cut forest meets the rim exactly at its original terminal points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

/-- A cut point on the actual section rim is an original terminal point, never an
interior point of a finite or terminal edge. -/
theorem exists_terminalPoint_of_mem_truncatedCarrier_frontier {p : Plane}
    (on_cut : p ∈ R.truncatedCarrier level higher)
    (on_rim : p ∈ frontier {x | G.height x ≤ level}) :
    ∃ r : {v // v ∈ R.parents.roots}, p = R.terminalPoint level r := by
  obtain ⟨v, member⟩ := Set.mem_iUnion.mp on_cut
  obtain ⟨t, bounds, at_point⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
  have final : p = R.truncatedPoint level ((R.truncatedParents level higher).parent (.inl v)) := by
    by_contra different
    have before : t < 1 := by
      by_contra after
      have same : t = 1 := le_antisymm bounds.2 (le_of_not_gt after)
      apply different
      simpa only [same, AffineMap.lineMap_apply_one] using at_point.symm
    have below : G.height p < level := by
      by_cases zero : t = 0
      · have same : p = K.projectedVertex v := by
          simpa only [zero, AffineMap.lineMap_apply_zero, truncatedPoint] using at_point.symm
        exact same ▸ higher v
      · apply R.truncated_segment_height_lt level higher v
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨lt_of_le_of_ne bounds.1 (Ne.symm zero), before⟩, at_point⟩
    exact on_rim.2 (G.mem_interior_sublevel below)
  cases parent : (R.truncatedParents level higher).parent (.inl v) with
  | inl w =>
    rw [parent] at final
    have below : G.height p < level := final ▸ higher w
    exact (on_rim.2 (G.mem_interior_sublevel below)).elim
  | inr r =>
    rw [parent] at final
    exact ⟨r, final⟩

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)

include no_boundary in
/-- Embedded original rays give a unique named original terminal point at every rim cut. -/
theorem existsUnique_terminalPoint_of_mem_truncatedCarrier_frontier {p : Plane}
    (on_cut : p ∈ R.truncatedCarrier level higher)
    (on_rim : p ∈ frontier {x | (K.clippedExtension slopes compact nonempty).height x ≤ level}) :
    ∃! r : {v // v ∈ R.parents.roots}, p = R.terminalPoint level r := by
  obtain ⟨r, same⟩ := R.exists_terminalPoint_of_mem_truncatedCarrier_frontier level higher on_cut
    on_rim
  refine ⟨r, same, fun s at_s => ?_⟩
  have indices := K.truncatedPoint_injective compact nonempty R no_boundary level higher
    (show R.truncatedPoint level (.inr s) = R.truncatedPoint level (.inr r) from
      at_s.symm.trans same)
  exact Sum.inr.inj indices

end Unfoldings.ConvexRoof
