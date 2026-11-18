module

public import Unfoldings.Roof.RestoredWholeTerminalBanks
public import Unfoldings.Geometry.SpatialEnvelopeCutFiber

/-! An unchanged local terminal cut germ fixes the entire original bank-side label. -/

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

local instance restoredTerminalSideIndexFintype : Fintype W.Index := W.finiteIndex

variable (cuts : Set Plane) (included : cuts ⊆ R.carrier)

/-- At a retained genuine terminal cut, opposite original side labels remain distinct. -/
theorem restoredWholeTerminalBank_side_injective_of_germ
    (r : {v // v ∈ R.parents.roots}) (t : ℝ≥0) (positive : 0 < t.val)
    {ε : ℝ} (radius : 0 < ε)
    (germ : ∀ z, dist z (R.exterior.ray (R.terminalIndex r) t.val) < ε →
      (z ∈ R.carrier ↔ z ∈ cuts)) :
    Function.Injective (fun side =>
      K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side t) := by
  intro side other equal
  by_cases same : side = other
  · exact same
  · apply (K.wholeTerminalBank_ne compact nonempty R no_boundary W r side other same t t
      positive).elim
    apply W.partition.forgetCut_injective_at_of_local_eq R.carrier cuts included
      (K.wholeTerminalBank compact nonempty R no_boundary W r side t) radius ?_
      (K.wholeTerminalBank compact nonempty R no_boundary W r other t) equal
    intro z near
    have point := (congrArg Cap.horizontal
      (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t)).trans
      (SpatialEnvelope.horizontal_point _ _)
    exact germ z (by rwa [point] at near)

/-- The actual endpoint copy determines its unique original terminal bank side whenever
restoration keeps the original local cut. No choice of an incident side is supplied. -/
theorem existsUnique_restoredWholeTerminalBank_side_of_germ
    (r : {v // v ∈ R.parents.roots}) (t : ℝ≥0) (positive : 0 < t.val)
    (x : W.partition.Cut cuts)
    (position : Cap.horizontal (W.partition.restoreCut cuts x).val =
      R.exterior.ray (R.terminalIndex r) t.val)
    {ε : ℝ} (radius : 0 < ε)
    (germ : ∀ z, dist z (R.exterior.ray (R.terminalIndex r) t.val) < ε →
      (z ∈ R.carrier ↔ z ∈ cuts)) :
    ∃! side : Bool,
      x = K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side t := by
  obtain ⟨side, at_x⟩ := K.exists_restoredWholeTerminalBank_side compact nonempty R no_boundary W
    cuts included r t positive x position
  refine ⟨side, at_x, fun other same => ?_⟩
  exact K.restoredWholeTerminalBank_side_injective_of_germ compact nonempty R no_boundary W
    cuts included r t positive radius germ (same.symm.trans at_x)

end Unfoldings.ConvexRoof
