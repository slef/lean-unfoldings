module

public import Unfoldings.Roof.CompatibleTerminalFiberBanks
public import Unfoldings.Metric.ForwardBankParameter

/-! Continue an actual whole-cut endpoint along its uniquely determined original terminal side. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance wholeTerminalContinuationIndexFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (time : ℝ≥0) (positive : 0 < time.val)
  (x : W.Cut)
  (position : Cap.horizontal (W.partition.restoreCut R.carrier x).val =
    R.exterior.ray (R.terminalIndex r) time.val)

/-- The actual endpoint determines this side uniquely; no orientation certificate is supplied. -/
def wholeTerminalContinuationSide : Bool :=
  (K.existsUnique_wholeTerminalBank_side compact nonempty R no_boundary W r time positive
    x position).choose

/-- Continue on the original bank at its original physical speed after the supplied endpoint. -/
def wholeTerminalContinuation (speed : ℝ≥0) (t : ℝ≥0) : W.Cut :=
  K.wholeTerminalBank compact nonempty R no_boundary W r
    (K.wholeTerminalContinuationSide compact nonempty R no_boundary W r time positive x position)
    (forwardBankParameter time speed t)

/-- The completed tail begins at the literal original metric endpoint copy. -/
@[simp] theorem wholeTerminalContinuation_zero (speed : ℝ≥0) :
    K.wholeTerminalContinuation compact nonempty R no_boundary W r time positive x position
      speed 0 = x := by
  simp only [wholeTerminalContinuation, forwardBankParameter_zero]
  exact ((K.existsUnique_wholeTerminalBank_side compact nonempty R no_boundary W r time
    positive x position).choose_spec.1).symm

/-- Every tail point keeps its original spatial roof coordinates. -/
theorem restore_wholeTerminalContinuation (speed t : ℝ≥0) :
    (W.partition.restoreCut R.carrier
      (K.wholeTerminalContinuation compact nonempty R no_boundary W r time positive x position
        speed t)).val = SpatialEnvelope.point M.plane
      (R.exterior.ray (R.terminalIndex r) (time.val + speed.val * t.val)) :=
  K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r _ _

/-- This entire unbounded continuation retains its exact physical metric speed. -/
theorem edist_wholeTerminalContinuation (speed s t : ℝ≥0) :
    edist (K.wholeTerminalContinuation compact nonempty R no_boundary W r time positive x
        position speed s)
      (K.wholeTerminalContinuation compact nonempty R no_boundary W r time positive x
        position speed t) =
      ((‖R.exterior.spatialDirection (R.terminalIndex r)‖₊ : ℝ≥0∞) * speed) * edist s t := by
  rw [wholeTerminalContinuation, wholeTerminalContinuation, K.edist_wholeTerminalBank,
    edist_forwardBankParameter, mul_assoc]

end Unfoldings.ConvexRoof
