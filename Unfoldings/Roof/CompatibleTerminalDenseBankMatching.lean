module

public import Unfoldings.Roof.CompatibleTerminalFiberBanks

/-! A connected dense positive bank portion determines all original endpoint copies. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance denseTerminalBankIndexFintype : Fintype W.Index := W.finiteIndex

/-- Matching on a connected dense positive portion fixes the named whole bank everywhere,
including any parameter-zero endpoint. Only the original spatial trace is supplied. -/
theorem wholeTerminalBank_side_of_dense_positive {A : Type*} [TopologicalSpace A]
    (r : {v // v ∈ R.parents.roots}) (curve : A → W.Cut) (continuous : Continuous curve)
    (time : A → ℝ≥0) (continuous_time : Continuous time) (S : Set A)
    (connected : IsPreconnected S) (dense : Dense S) (positive : ∀ t ∈ S, 0 < (time t).val)
    (position : ∀ t, Cap.horizontal (W.partition.restoreCut R.carrier (curve t)).val =
      R.exterior.ray (R.terminalIndex r) (time t).val) :
    ∃ side : Bool, ∀ t,
      curve t = K.wholeTerminalBank compact nonempty R no_boundary W r side (time t) := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace connected
  obtain ⟨side, same⟩ := K.wholeTerminalBank_side_constant compact nonempty R no_boundary W r
    (fun t : S => curve t.val) (continuous.comp continuous_subtype_val)
    (fun t : S => time t.val) (fun t => positive t.val t.property) (fun t => position t.val)
  have agrees : Set.EqOn curve
      (fun t => K.wholeTerminalBank compact nonempty R no_boundary W r side (time t)) S :=
    fun t ht => same ⟨t, ht⟩
  exact ⟨side, fun t => agrees.closure continuous
    ((Dilation.lipschitzWith (K.wholeTerminalBank compact nonempty R no_boundary W r side)
      ).continuous.comp continuous_time) (dense t)⟩

end Unfoldings.ConvexRoof
