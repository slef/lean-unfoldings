module

public import Unfoldings.Roof.CompatiblePartialCutPartitionIndependence
public import Unfoldings.Roof.CompatibleWindowModel
public import Unfoldings.Geometry.SpatialEnvelopeWindowCompact
public import Unfoldings.Metric.LocalChartTargetTransport

/-! Actual windows retain whole neighborhoods for every closed partial original forest cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  {J : Type} {equations : J → Plane →ᵃ[ℝ] ℝ}
  (V : R.WindowModel M equations) (W : R.WholeCutModel M)

local instance partialWindowPatchIndexFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance partialOriginalWindowPatchIndexFintype : Fintype W.Index := W.finiteIndex

variable (cuts : Set Plane) (closed : IsClosed cuts) (included : cuts ⊆ R.carrier)

/-- The original physical cut patch inside the actual aligned polygonal window. -/
abbrev PartialPatch := V.whole.partition.WindowCut V.signs cuts

/-- Include the actual window patch into any retained original model of this forest cut. -/
@[macro_inline] def partialPatchMap (source : V.PartialPatch cuts) : W.partition.Cut cuts :=
  (W.partialCutModelEquiv V.whole cuts closed included).symm (V.whole.partition.windowCutMap
    V.signs cuts source)

theorem partialPatchMap_lipschitz : LipschitzWith 1 (V.partialPatchMap W cuts closed included) := by
  intro x y
  exact ((W.partialCutModelEquiv V.whole cuts closed included).symm.isometry.edist_eq _ _).trans_le
    (V.whole.partition.windowCutMap_lipschitz V.signs cuts x y)

/-- The actual patch inclusion retains its original physical roof point. -/
theorem restore_partialPatchMap (source : V.PartialPatch cuts) :
    W.partition.restoreCut cuts (V.partialPatchMap W cuts closed included source) =
      V.whole.partition.restoreCut cuts
        (V.whole.partition.windowCutMap V.signs cuts source) :=
  map_isometry_symm (W.partialCutModelEquiv V.whole cuts closed included) (W.partition.restoreCut
    cuts)
    (V.whole.partition.restoreCut cuts) (W.restore_partialCutModelEquiv V.whole cuts closed
      included) _

/-- A compact polygonal window constructs a compact intrinsic metric patch of the original cut. -/
theorem partialPatch_compactSpace (compact : IsCompact {z | ∀ j, 0 ≤ equations j z}) :
    CompactSpace (V.PartialPatch cuts) :=
  V.whole.partition.windowCut_compactSpace equations V.signs V.aligned compact cuts

/-- Every original partial-forest cut copy in the strict window interior has an exact whole
intrinsic ball in the actual window patch, regardless of the chosen original partition. -/
theorem exists_partialPatch_ball_chart (x : W.partition.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut cuts x).val)) :
    ∃ source : V.PartialPatch cuts, V.partialPatchMap W cuts closed included source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (B z).val = V.partialPatchMap W cuts closed
          included z.val := by
  exact exists_ball_chart_isometry_target_of_fold (W.partialCutModelEquiv V.whole cuts closed
    included)
    (V.whole.partition.windowCutMap V.signs cuts)
    (W.partition.restoreCut cuts) (V.whole.partition.restoreCut cuts)
    (fun p => ∀ j, 0 < equations j (Cap.horizontal p.val))
    (W.restore_partialCutModelEquiv V.whole cuts closed included)
    (fun y positive => V.whole.partition.exists_windowCut_ball_chart
      equations V.signs V.aligned cuts y positive) x positive

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
