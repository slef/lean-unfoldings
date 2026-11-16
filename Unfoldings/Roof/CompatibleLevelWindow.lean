module

public import Unfoldings.Roof.CompatibleWindowModel
public import Unfoldings.Roof.TruncatedCutSegments
public import Unfoldings.Geometry.SpatialEnvelopeLevelWindow

/-! Canonical actual window models at the chosen finite completion height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β) (M : G.FiniteSlopeModel)
  (level : ℝ) (higher : ∀ v, G.height (K.projectedVertex v) < level)

include R higher
/-- The chosen common truncation level supplies a strict original interior point. -/
theorem levelWindow_higher : -level < SpatialEnvelope.height M.plane R.cutInteriorPoint := by
  rw [M.height_eq]
  have bound := R.cutInteriorPoint_height level higher
  linarith

/-- The canonical completion-window equations are all proper. -/
theorem levelWindow_proper (i : M.Face) :
    SpatialEnvelope.levelEquation M.plane (-level) i ≠ 0 :=
  SpatialEnvelope.levelEquation_ne_zero M.plane (-level) (R.levelWindow_higher M level higher) i

/-- The actual completion window has nonempty interior. -/
theorem levelWindow_full :
    (interior {p | ∀ i, 0 ≤ SpatialEnvelope.levelEquation M.plane (-level) i p}).Nonempty :=
  SpatialEnvelope.levelEquation_full M.plane (-level) (R.levelWindow_higher M level higher)

/-- Construct a retained whole-forest model aligned to the actual completion-height window. -/
def levelWindowModel : R.WindowModel M (SpatialEnvelope.levelEquation M.plane (-level)) :=
  R.windowModel M _ (R.levelWindow_proper M level higher)

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
