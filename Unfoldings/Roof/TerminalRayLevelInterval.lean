module

public import Unfoldings.Roof.TruncatedWholeCarrier

/-! Exact strict level bounds on every original terminal-ray parameter. -/

@[expose] public section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

include higher in
/-- A terminal ray lies strictly below the completion height exactly before its terminal time. -/
theorem terminal_ray_below_iff (r : {v // v ∈ R.parents.roots}) {t : ℝ} (nonnegative : 0 ≤ t) :
    G.height (R.exterior.ray (R.terminalIndex r) t) < level ↔ t < R.terminalTime level r := by
  have at_time := R.terminalPoint_level level higher r
  change G.height (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r)) = level at at_time
  rw [R.exterior.height_ray _ (R.terminalTime_pos level higher r).le] at at_time
  rw [R.exterior.height_ray _ nonnegative]
  have rate : 0 < R.exterior.rate (R.terminalIndex r) :=
    R.exterior.positive (R.terminalIndex r)
  constructor <;> intro bound <;> nlinarith

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
