module

public import Unfoldings.Roof.TruncatedCutSegments
public import Unfoldings.Roof.CompatibleCutClosed

/-! The bounded compatible cut is exactly the full original cut inside the chosen level. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

include higher in
/-- A terminal ray is in the truncation sublevel precisely up to its actual terminal time. -/
theorem terminal_ray_sublevel_iff (r : {v // v ∈ R.parents.roots}) {t : ℝ} (nonnegative : 0 ≤ t) :
    G.height (R.exterior.ray (R.terminalIndex r) t) ≤ level ↔ t ≤ R.terminalTime level r := by
  have at_time := R.terminalPoint_level level higher r
  change G.height (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) = level at at_time
  rw [R.exterior.height_ray _ (R.terminalTime_pos level higher r).le] at at_time
  rw [R.exterior.height_ray _ nonnegative]
  have rate : 0 < R.exterior.rate (R.terminalIndex r) :=
    R.exterior.positive (R.terminalIndex r)
  constructor <;> intro bound <;> nlinarith

/-- The chosen finite cut retains every point of the original whole cut in the closed
sublevel, including the truncation endpoints of every terminal ray. -/
theorem truncatedCarrier_eq_carrier_inter_sublevel :
    R.truncatedCarrier level higher = R.carrier ∩ {x | G.height x ≤ level} := by
  classical
  apply Set.Subset.antisymm
  · intro p member
    refine ⟨?_, R.truncatedCarrier_subset_sublevel level higher member⟩
    obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp member
    by_cases root : v ∈ R.parents.roots
    · have parent : (R.truncatedParents level higher).parent (.inl v) = .inr ⟨v, root⟩ :=
        R.parents.withLeaves_parent_root level _ ⟨v, root⟩
      rw [parent] at on_edge
      change p ∈ segment ℝ (K.projectedVertex v) (R.terminalPoint level ⟨v, root⟩) at on_edge
      obtain ⟨t, ht, equal⟩ := (segment_eq_image_lineMap ℝ _ _).subset on_edge
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨v, root⟩,
        t * R.terminalTime level ⟨v, root⟩,
        mul_nonneg ht.1 (R.terminalTime_pos level higher ⟨v, root⟩).le,
        equal.symm.trans (R.terminal_lineMap_eq_ray level ⟨v, root⟩ t)⟩)
    · have parent : (R.truncatedParents level higher).parent (.inl v) =
          .inl (R.parents.parent v) := R.parents.withLeaves_parent_nonroot level _ root
      rw [parent] at on_edge
      exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v, root⟩, on_edge⟩)
  · rintro p ⟨finite | infinite, below⟩
    · obtain ⟨v, on_edge⟩ := Set.mem_iUnion.mp finite
      apply Set.mem_iUnion.mpr
      refine ⟨v.val, ?_⟩
      have parent : (R.truncatedParents level higher).parent (.inl v.val) =
          .inl (R.parents.parent v.val) :=
        R.parents.withLeaves_parent_nonroot level _ v.property
      rw [parent]
      exact on_edge
    · obtain ⟨r, t, nonnegative, equal⟩ := Set.mem_iUnion.mp infinite
      have before : t ≤ R.terminalTime level r :=
        (R.terminal_ray_sublevel_iff level higher r nonnegative).mp
          (Eq.mp (congrArg (fun q : Plane => G.height q ≤ level) equal) below)
      apply Set.mem_iUnion.mpr
      refine ⟨r.val, ?_⟩
      have parent : (R.truncatedParents level higher).parent (.inl r.val) = .inr r :=
        R.parents.withLeaves_parent_root level _ r
      rw [parent]
      change p ∈ segment ℝ (K.projectedVertex r.val) (R.terminalPoint level r)
      apply (segment_eq_image_lineMap ℝ _ _).symm.subset
      refine ⟨t / R.terminalTime level r, ⟨div_nonneg nonnegative
        (R.terminalTime_pos level higher r).le,
        (div_le_one (R.terminalTime_pos level higher r)).mpr before⟩, ?_⟩
      rw [R.terminal_lineMap_eq_ray, div_mul_cancel₀ _ (R.terminalTime_pos level higher r).ne']
      exact equal.symm

/-- Membership in the full cut and the truncated cut agrees throughout the closed sublevel. -/
theorem mem_truncatedCarrier_iff {p : Plane} (below : G.height p ≤ level) :
    p ∈ R.truncatedCarrier level higher ↔ p ∈ R.carrier := by
  rw [R.truncatedCarrier_eq_carrier_inter_sublevel level higher]
  exact and_iff_left below

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
