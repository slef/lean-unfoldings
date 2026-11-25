module

public import Unfoldings.Roof.AffineFloorNormalCells
public import Unfoldings.Roof.SelectorCurvatureBudget

/-! The original selector controls the curvature of any aligned affine-floor mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

open MeasureTheory
open scoped ENNReal

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel) {Z : ℝ}
  {J : Type} {extra : J → Plane →ᵃ[ℝ] ℝ} {floor : Plane →ᵃ[ℝ] ℝ}
  (T : SpatialEnvelope.FloorMesh M.plane floor extra Z)
  (inside : (interior (SpatialEnvelope.clipAbove M.plane floor Z)).Nonempty)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

include inside in
/-- Refining the roof along original seams and exit rays leaves the same
selector area bound for its actual total intrinsic curvature. -/
theorem floorRoof_curvature_le_selector_volume (convex : Convex ℝ E.slopes) :
    ENNReal.ofReal (T.pairedComplex.totalInteriorAngularDefect Set.univ) ≤ volume E.slopes := by
  apply (T.roof inside).ofReal_totalCurvature_le_selector_volume convex
  intro f
  change (M.plane (T.support f)).normalSlope ∈ E.slopes
  rw [M.normalSlope]
  exact M.included _ (T.support f).property

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
