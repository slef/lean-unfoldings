module

public import Unfoldings.Roof.CompatibleMeshCurveLift
public import Unfoldings.Roof.TerminalRayLevelInterval
public import Unfoldings.Roof.CompatibleWholeTerminalBanks
public import Unfoldings.Metric.HalfOpenIntervalExtension

/-! Construct the actual finite terminal banks as restrictions of the original whole banks. -/

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
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance constructedTerminalIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "B" => SlopeEnvelope.boundaryEnvelope
  (K.clippedExtension slopes compact nonempty) boundary
local notation "Gcut" => K.truncatedCutEmbedding compact nonempty R no_boundary level higher


local notation "V" => R.levelWindowModel M level higher
local notation "proper" => R.levelWindow_proper M level higher
local notation "full" => R.levelWindow_full M level higher
local notation "domain" => SpatialEnvelope.levelEquation_domain M.plane (-level)
local notation "heights" => (Set.eqOn_refl (SpatialEnvelope.height M.plane) _)
local notation "outside" => K.compatibleMesh_cut_disjoint_interior compact nonempty R
  no_boundary level higher M positive inner_disk
local notation "removed" => K.compatibleMesh_removed_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "retained" => K.compatibleMesh_retained_open_edge compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

variable (W : R.WholeCutModel M)

local instance constructedTerminalWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "τ" => R.terminalTime level r
local notation "bank" => K.wholeTerminalBank compact nonempty R no_boundary W r side

/-- The original whole terminal bank before the finite completion endpoint. -/
@[macro_inline] def compatibleMeshTerminalCurve : Set.Ico (0 : ℝ) τ → W.Cut :=
  bank ∘ nonnegativeIcoParameter

include higher in
theorem compatibleMeshTerminalCurve_below (t : Set.Ico (0 : ℝ) τ) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut R.carrier
        (K.compatibleMeshTerminalCurve compact nonempty R no_boundary level M W r side t)).val) <
          level := by
  have projected := (congrArg Cap.horizontal
    (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side
      ⟨t.val, t.property.1⟩)).trans (SpatialEnvelope.horizontal_point M.plane _)
  exact (congrArg (K.clippedExtension slopes compact nonempty).height projected).trans_lt
    ((R.terminal_ray_below_iff level higher r t.property.1).mpr t.property.2)

theorem compatibleMeshTerminalCurve_lipschitz : LipschitzWith (Dilation.ratio bank)
    (K.compatibleMeshTerminalCurve compact nonempty R no_boundary level M W r side) :=
  dilation_comp_isometry_lipschitz bank _ nonnegativeIcoParameter_isometry

/-- The uniquely determined finite lift of the actual original terminal bank. -/
def compatibleMeshTerminalLift : Set.Ico (0 : ℝ) τ →
    (T).pairedComplex.Realization (Fcut).retain :=
  K.compatibleMeshCurveLift compact nonempty R no_boundary level higher M positive inner_disk
    beta acute W (Set.Ico (0 : ℝ) τ)
    (K.compatibleMeshTerminalCurve compact nonempty R no_boundary level M W r side)
    (K.compatibleMeshTerminalCurve_below compact nonempty R no_boundary level higher M W r side)

theorem compatibleMeshTerminalLift_lipschitz : LipschitzWith (Dilation.ratio bank)
    (K.compatibleMeshTerminalLift compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W r side) :=
  K.compatibleMeshCurveLift_lipschitz compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W (Set.Ico (0 : ℝ) τ) _ _ (convex_Ico 0 τ)
    (K.compatibleMeshTerminalCurve_lipschitz compact nonempty R no_boundary level M W r side)

@[simp] theorem compatibleMeshWholeMap_terminalLift (t : Set.Ico (0 : ℝ) τ) :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W (K.compatibleMeshTerminalLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side t) = bank ⟨t.val, t.property.1⟩ :=
  K.compatibleMeshWholeMap_curveLift compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W _ _ _ t

/-- Complete the actual finite terminal bank at its original truncation endpoint. -/
def compatibleMeshTerminalBank : Set.Icc (0 : ℝ) τ →
    (T).pairedComplex.Realization (Fcut).retain :=
  extendHalfOpenInterval (R.terminalTime_pos level higher r)
    (K.compatibleMeshTerminalLift compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W r side)

theorem compatibleMeshTerminalBank_lipschitz : LipschitzWith (Dilation.ratio bank)
    (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W r side) :=
  extendHalfOpenInterval_lipschitz _ _
    (K.compatibleMeshTerminalLift_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)

/-- The constructed finite bank is the actual whole-bank restriction, including both endpoints. -/
@[simp] theorem compatibleMeshWholeMap_terminalBank (t : Set.Icc (0 : ℝ) τ) :
    K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W (K.compatibleMeshTerminalBank compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W r side t) = bank ⟨t.val, t.property.1⟩ := by
  have continuous_bank : Continuous (fun t : Set.Icc (0 : ℝ) τ =>
      bank ⟨t.val, t.property.1⟩) :=
    (Dilation.lipschitzWith bank).continuous.comp (continuous_subtype_val.subtype_mk _)
  exact map_extendHalfOpenInterval (R.terminalTime_pos level higher r) _
    (K.compatibleMeshTerminalLift_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side)
    (K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M positive inner_disk
      beta acute W)
    (K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W).continuous _ continuous_bank
    (K.compatibleMeshWholeMap_terminalLift compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side) t

end Unfoldings.ConvexRoof
