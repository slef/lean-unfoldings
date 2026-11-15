module

public import Unfoldings.Roof.CompatibleTerminalFiber
public import Unfoldings.Metric.PositiveHalflineExtension
public import Mathlib.Topology.MetricSpace.Dilation

/-! Complete whole terminal banks in the full original forest cut, including their endpoints. -/

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

local instance terminalCompletionIndexFintype : Fintype W.Index := W.finiteIndex
local instance terminalCompletionComplete : CompleteSpace W.Cut := W.complete

/-- Lift the entire closed bank by completing its uniquely determined positive part. -/
def terminalClosedRayLift (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) : ℝ≥0 → W.Cut :=
  extendPositiveHalfline (K.terminalRayLift compact nonempty R no_boundary W r
    (fun t => g ⟨t.val, t.property.le⟩) (fun t => position ⟨t.val, t.property.le⟩))

theorem terminalClosedRayLift_lipschitz (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    {c : ℝ≥0} (bounded : LipschitzWith c g) :
    LipschitzWith c (K.terminalClosedRayLift compact nonempty R no_boundary W r g position) := by
  apply extendPositiveHalfline_lipschitz
  apply K.terminalRayLift_lipschitz compact nonempty R no_boundary W r _ _ c
  intro s t
  exact bounded ⟨s.val, s.property.le⟩ ⟨t.val, t.property.le⟩

/-- Restoring the other cuts recovers the entire supplied bank, including the completed endpoint. -/
@[simp] theorem forgetCut_terminalClosedRayLift (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    {c : ℝ≥0} (bounded : LipschitzWith c g) (t : ℝ≥0) :
    W.partition.forgetCut R.carrier (R.terminalRayCut r) (R.terminalRayCut_subset_carrier r)
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position t) = g t := by
  let h := K.terminalRayLift compact nonempty R no_boundary W r
    (fun s => g ⟨s.val, s.property.le⟩) (fun s => position ⟨s.val, s.property.le⟩)
  have bounded_h : LipschitzWith c h :=
    K.terminalRayLift_lipschitz compact nonempty R no_boundary W r _ _ c
      (fun s u => bounded ⟨s.val, s.property.le⟩ ⟨u.val, u.property.le⟩)
  exact map_extendPositiveHalfline h bounded_h
    (W.partition.forgetCut R.carrier (R.terminalRayCut r) (R.terminalRayCut_subset_carrier r))
    (W.partition.forgetCut_lipschitz R.carrier (R.terminalRayCut r)
      (R.terminalRayCut_subset_carrier r)).continuous g bounded.continuous
    (fun s => K.forgetCut_terminalRayLift compact nonempty R no_boundary W r _ _ s) t

/-- The completed bank retains its actual original spatial roof points. -/
theorem restoreCut_terminalClosedRayLift (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 → W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    {c : ℝ≥0} (bounded : LipschitzWith c g) (t : ℝ≥0) :
    W.partition.restoreCut R.carrier
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position t) =
        W.partition.restoreCut (R.terminalRayCut r) (g t) :=
  (W.partition.restoreCut_forgetCut R.carrier (R.terminalRayCut r)
    (R.terminalRayCut_subset_carrier r) _).symm.trans
      (congrArg (W.partition.restoreCut (R.terminalRayCut r))
        (K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r g position bounded t))

/-- Whole-bank distances survive lifting to the full forest cut, including the endpoint. -/
theorem edist_terminalClosedRayLift (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 →ᵈ W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) (s t : ℝ≥0) :
    edist (K.terminalClosedRayLift compact nonempty R no_boundary W r g position s)
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position t) =
        edist (g s) (g t) := by
  apply le_antisymm
  · exact (K.terminalClosedRayLift_lipschitz compact nonempty R no_boundary W r g position
      (Dilation.lipschitzWith g) s t).trans_eq (Dilation.edist_eq g s t).symm
  · have bound := W.partition.forgetCut_lipschitz R.carrier (R.terminalRayCut r)
      (R.terminalRayCut_subset_carrier r)
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position s)
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position t)
    simpa only [K.forgetCut_terminalClosedRayLift compact nonempty R no_boundary W r g position
      (Dilation.lipschitzWith g), ENNReal.coe_one, one_mul] using bound

/-- The original full-forest bank is a dilation of the entire closed half-line. -/
def terminalClosedRayLiftDilation (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 →ᵈ W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) : ℝ≥0 →ᵈ W.Cut where
  toFun := K.terminalClosedRayLift compact nonempty R no_boundary W r g position
  edist_eq' := ⟨Dilation.ratio g, Dilation.ratio_ne_zero g, fun s t =>
    (K.edist_terminalClosedRayLift compact nonempty R no_boundary W r g position s t).trans
      (Dilation.edist_eq g s t)⟩

theorem terminalClosedRayLift_isClosedEmbedding (r : {v // v ∈ R.parents.roots})
    (g : ℝ≥0 →ᵈ W.partition.Cut (R.terminalRayCut r))
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut (R.terminalRayCut r) (g t)).val =
      R.exterior.ray (R.terminalIndex r) t.val) :
    Topology.IsClosedEmbedding
      (K.terminalClosedRayLift compact nonempty R no_boundary W r g position) :=
  Dilation.isClosedEmbedding
    (K.terminalClosedRayLiftDilation compact nonempty R no_boundary W r g position)

end Unfoldings.ConvexRoof
