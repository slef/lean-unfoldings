module

public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Roof.TruncatedCutSegments
public import Unfoldings.Roof.TruncatedCutEmbedding

/-! The last fine routing step reaches a uniquely named original terminal ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

include higher in
/-- A routing step ending at the truncation level lies on a terminal ray, since
all original finite parent segments lie strictly below that level. -/
theorem followsStep_at_level {x y : Plane} (step : R.FollowsStep x y)
    (at_level : G.height y = level) :
    ∃ r : {v // v ∈ R.parents.roots}, ∃ s : ℝ,
      0 ≤ s ∧ s ≤ R.terminalTime level r ∧
      x = R.exterior.ray (R.terminalIndex r) s ∧ y = R.terminalPoint level r := by
  rcases step with ⟨v, s, t, hs, order, ht, first, last⟩ |
    ⟨r, s, t, hs, order, first, last⟩
  · have in_segment : y ∈ segment ℝ (K.projectedVertex v.val)
        (K.projectedVertex (R.parents.parent v.val)) := by
      rw [last]
      change K.projectedVertex v.val + t •
        (K.projectedVertex (R.parents.parent v.val) - K.projectedVertex v.val) ∈ _
      have interpolation := lineMap_mem_segment ℝ (K.projectedVertex v.val)
        (K.projectedVertex (R.parents.parent v.val)) ⟨hs.trans order, ht⟩
      simpa only [AffineMap.lineMap_apply_module', add_comm] using interpolation
    obtain ⟨u, bounds, at_y⟩ := (segment_eq_image_lineMap ℝ _ _).subset in_segment
    have bound : G.height y < level := by
      by_cases initial : u = 0
      · have same : y = K.projectedVertex v.val := by
          simpa only [initial, AffineMap.lineMap_apply_zero] using at_y.symm
        exact same ▸ higher v.val
      by_cases terminal : u = 1
      · have same : y = K.projectedVertex (R.parents.parent v.val) := by
          simpa only [terminal, AffineMap.lineMap_apply_one] using at_y.symm
        exact same ▸ higher _
      · apply G.openSegment_height_lt (higher v.val) (higher (R.parents.parent v.val)).le
        rw [openSegment_eq_image_lineMap]
        exact ⟨u, ⟨lt_of_le_of_ne bounds.1 (Ne.symm initial),
          lt_of_le_of_ne bounds.2 terminal⟩, at_y⟩
    exact (ne_of_lt bound at_level).elim
  · have nonnegative := hs.trans order
    have end_level := R.terminalPoint_level level higher r
    rw [last, R.exterior.height_ray _ nonnegative] at at_level
    change G.height (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) =
      level at end_level
    rw [R.exterior.height_ray _ (R.terminalTime_pos level higher r).le] at end_level
    have time : t = R.terminalTime level r := by
      have rate : 0 < R.exterior.rate (R.terminalIndex r) := R.exterior.positive _
      nlinarith
    exact ⟨r, s, hs, time ▸ order, first, last.trans (congrArg (R.exterior.ray _) time)⟩

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

include no_boundary higher in
/-- A genuine last fine step reaches a named terminal point along that very original ray,
strictly before its terminal time. No terminal-ray correspondence is input. -/
theorem followsStep_to_terminalPoint (r : {v // v ∈ R.parents.roots}) {x : Plane}
    (step : R.FollowsStep x (R.terminalPoint level r))
    (different : x ≠ R.terminalPoint level r) :
    ∃ s : ℝ, 0 ≤ s ∧ s < R.terminalTime level r ∧
      x = R.exterior.ray (R.terminalIndex r) s := by
  obtain ⟨other, s, nonnegative, before, first, last⟩ :=
    R.followsStep_at_level level higher step (R.terminalPoint_level level higher r)
  have same : other = r := by
    apply Sum.inr.inj
    exact K.truncatedPoint_injective compact nonempty R no_boundary level higher
      (show R.truncatedPoint level (.inr other) = R.truncatedPoint level (.inr r) from last.symm)
  subst other
  refine ⟨s, nonnegative, lt_of_le_of_ne before ?_, first⟩
  intro equal
  exact different (first.trans (congrArg (R.exterior.ray _) equal))

end Unfoldings.ConvexRoof
