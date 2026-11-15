module

public import Unfoldings.Roof.CompatibleWindowModel
public import Unfoldings.Geometry.SpatialEnvelopeWindowCompact
public import Unfoldings.Metric.LocalChartTargetTransport

/-! Actual compact window patches retain original interior forest-cut neighborhoods. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  {R : K.CompatiblePotentialRouting U G boundary a β} {M : G.FiniteSlopeModel}
  {J : Type} {equations : J → Plane →ᵃ[ℝ] ℝ}
  (V : R.WindowModel M equations) (W : R.WholeCutModel M)

local instance windowPatchIndexFintype : Fintype V.whole.Index := V.whole.finiteIndex
local instance originalWindowPatchIndexFintype : Fintype W.Index := W.finiteIndex

/-- The original physical cut patch inside the actual aligned polygonal window. -/
abbrev Patch := V.whole.partition.WindowCut V.signs R.carrier

/-- Include the actual window patch into any retained original model of this forest cut. -/
@[macro_inline] def patchMap (source : V.Patch) : W.Cut :=
  (W.cutModelEquiv V.whole).symm (V.whole.partition.windowCutMap V.signs R.carrier source)

theorem patchMap_lipschitz : LipschitzWith 1 (V.patchMap W) := by
  intro x y
  exact ((W.cutModelEquiv V.whole).symm.isometry.edist_eq _ _).trans_le
    (V.whole.partition.windowCutMap_lipschitz V.signs R.carrier x y)

/-- The actual patch inclusion retains its original physical roof point. -/
theorem restore_patchMap (source : V.Patch) :
    W.partition.restoreCut R.carrier (V.patchMap W source) =
      V.whole.partition.restoreCut R.carrier
        (V.whole.partition.windowCutMap V.signs R.carrier source) :=
  map_isometry_symm (W.cutModelEquiv V.whole) (W.partition.restoreCut R.carrier)
    (V.whole.partition.restoreCut R.carrier) (W.restore_cutModelEquiv V.whole) _

/-- A compact polygonal window constructs a compact intrinsic metric patch of the original cut. -/
theorem patch_compactSpace (compact : IsCompact {z | ∀ j, 0 ≤ equations j z}) :
    CompactSpace V.Patch :=
  V.whole.partition.windowCut_compactSpace equations V.signs V.aligned compact R.carrier

/-- Every original full-forest cut copy in the strict window interior has an exact whole
intrinsic ball in the actual window patch, regardless of the chosen original partition. -/
theorem exists_patch_ball_chart (x : W.Cut)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (W.partition.restoreCut R.carrier x).val)) :
    ∃ source : V.Patch, V.patchMap W source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (B z).val = V.patchMap W z.val := by
  exact exists_ball_chart_isometry_target_of_fold (W.cutModelEquiv V.whole)
    (V.whole.partition.windowCutMap V.signs R.carrier)
    (W.partition.restoreCut R.carrier) (V.whole.partition.restoreCut R.carrier)
    (fun p => ∀ j, 0 < equations j (Cap.horizontal p.val))
    (W.restore_cutModelEquiv V.whole)
    (fun y positive => V.whole.partition.exists_windowCut_ball_chart
      equations V.signs V.aligned R.carrier y positive) x positive

end Unfoldings.ConvexRoof.CompatiblePotentialRouting.WindowModel
