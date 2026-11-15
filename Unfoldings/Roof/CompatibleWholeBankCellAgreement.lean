module

public import Unfoldings.Roof.CompatibleWholeTerminalBanks
public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCellAgreement

/-! Constructed whole banks agree with the original retained partition-cell tails. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel.TerminalSupportCells

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  {W : R.WholeCutModel M} {r : {v // v ∈ R.parents.roots}} (B : W.TerminalSupportCells r)

local instance wholeBankCellIndexFintype : Fintype W.Index := W.finiteIndex

/-- On its actual original anchor tail, the whole one-ray bank is the original metric cell copy. -/
theorem oneRayBank_eq_liftCell (side : Bool) (t : ℝ≥0) (after : B.threshold ≤ t.val) :
    B.oneRayBank side t = W.partition.liftCell (R.terminalRayCut r) (B.anchor side)
      ⟨R.exterior.ray (R.terminalIndex r) t.val, B.tail side t.val after⟩ :=
  W.partition.faceSideRegionMap_eq_liftCell (B.anchor side)
    (orientMap (R.exterior.point (R.terminalIndex r)) (R.exterior.ray (R.terminalIndex r) 1))
    (orientMap_ne_zero (R.exterior.ray_endpoints_ne (R.terminalIndex r)))
    (W.terminalSigns r) (aligned_exterior (W := W)) (R.terminalRayCut r)
    (cut_closed (r := r)) (cut_level (r := r)) _ _ rfl

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WholeCutModel.TerminalSupportCells

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance fullWholeBankCellIndexFintype : Fintype W.Index := W.finiteIndex

/-- The whole full-forest bank is exactly the actual original anchor-cell tail, not merely
another isometric curve with the same spatial trace. -/
theorem wholeTerminalBank_eq_liftCell (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) (positive : 0 < t.val) (after : (W.terminalSupportCells r).threshold ≤ t.val) :
    K.wholeTerminalBank compact nonempty R no_boundary W r side t =
      W.partition.liftCell R.carrier ((W.terminalSupportCells r).anchor side)
        ⟨R.exterior.ray (R.terminalIndex r) t.val,
          (W.terminalSupportCells r).tail side t.val after⟩ := by
  let B := W.terminalSupportCells r
  let original := W.partition.liftCell R.carrier (B.anchor side)
    ⟨R.exterior.ray (R.terminalIndex r) t.val, B.tail side t.val after⟩
  let F := W.partition.forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r)
  have original_image : F original = B.oneRayBank side t :=
    (B.oneRayBank_eq_liftCell side t after).symm
  have bank_image : F (K.wholeTerminalBank compact nonempty R no_boundary W r side t) =
      B.oneRayBank side t := K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r
    (B.oneRayBankDilation side) (B.horizontal_restoreCut_oneRayBank side)
    (Dilation.lipschitzWith (B.oneRayBankDilation side)) t
  have unique := (K.existsUnique_terminalRayCut_preimage compact nonempty R no_boundary W r
    positive (B.oneRayBank side t) (B.horizontal_restoreCut_oneRayBank side t)).choose_spec
  exact (unique.2 _ bank_image).trans (unique.2 original original_image).symm

end Unfoldings.ConvexRoof
