module

public import Unfoldings.Roof.TerminalBands

/-! Keep original absolute ray time on finite terminal bands between two roof levels. -/

@[expose] public section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

/-- The finite outer band has a relative closed interval parameter with the original
absolute terminal-time offset. -/
theorem exists_terminal_band_parameter_of_mem_segment {level later : ℝ} (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) {p : Plane}
    (member : p ∈ segment ℝ (R.terminalPoint level r) (R.terminalPoint later r)) :
    ∃ t : Set.Icc (0 : ℝ) (R.terminalTime later r - R.terminalTime level r),
      p = R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + t.val) := by
  change p ∈ segment ℝ (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r))
    (R.exterior.ray (R.terminalIndex r) (R.terminalTime later r)) at member
  rw [← R.terminal_ray_interval r _ _ ((R.terminalTime_strictMono r) ordered).le] at member
  obtain ⟨s, bounds, at_p⟩ := member
  refine ⟨⟨s - R.terminalTime level r, sub_nonneg.mpr bounds.1,
    sub_le_sub_right bounds.2 _⟩, ?_⟩
  exact at_p.symm.trans (congrArg (R.exterior.ray (R.terminalIndex r)) (by ring))

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
