module

public import Unfoldings.Roof.CompatibleRootwardTerminalJoin
public import Unfoldings.Roof.CompatibleProcessedTerminalBanks
public import Unfoldings.Complex.BoundaryChainPath
public import Unfoldings.Topology.PathRayExtension
public import Unfoldings.Roof.CompatibleRootwardIntrinsicPath

/-! Whole unbounded intrinsic rootward banks with their original terminal tails. -/

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

local instance rootwardWholePathIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardWholePathWholeFintype : Fintype W.Index := W.finiteIndex

variable (r : {v // v ∈ R.parents.roots}) (side : Bool)

local notation "contour" => K.compatibleMeshRimContour compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W r side

local notation "SourceAt[" j "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "FrontierAt[" j "]" => TriangleComplex.contourFrontier
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) contour j
local notation "PathAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardPath compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "HistoryAt[" j "," k "]" =>
  K.compatibleMeshHistory compact nonempty R no_boundary level higher M
    positive inner_disk beta acute SourceAt[j] (k + 2)
local notation "RootAt[" s "," h "]" =>
  K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute s h

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S
local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "ChainAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk

local notation "MapAt[" j "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W FrontierAt[j]
local notation "EndAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W r side j h k hk
local notation "StartAt[" j "," h "," k "," hk "]" =>
  TriangleComplex.vertexPoint
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) _
    (TriangleComplex.boundaryEndVertex
      (SpatialEnvelope.Triangulation.pairedComplex
        (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) _
      (PairedInvolutions.System.Chain.first (ChainAt[j,h,k,hk])))

/-- Traverse the whole actual rootward bank without an outer truncation. The carrier is
closed and path connected, is exactly the original stem and original unbounded terminal tail,
and the two pieces meet only at their actual common intrinsic endpoint. -/
theorem exists_compatibleMeshCurrentRootward_whole_path
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    let root := RootAt[SourceAt[i],by omega]
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher _).le⟩
    let stem := K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length
    ∃ tailSide : Bool, ∃ P : ℝ≥0 → W.partition.Cut CutsAt[FrontierAt[i]],
      Continuous P ∧
      (∀ t : unitInterval, P ⟨t.val, t.property.1⟩ = stem t) ∧
      (∀ t : ℝ≥0, P (1 + t) = K.restoredWholeTerminalBank compact nonempty R no_boundary W
        CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] root tailSide (initial + t)) ∧
      Set.range P = MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) ∪
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
          IncludedAt[FrontierAt[i]] root tailSide) '' Set.Ici initial ∧
      IsClosed (Set.range P) ∧ IsPathConnected (Set.range P) ∧
      (MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length])) ∩
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
          IncludedAt[FrontierAt[i]] root tailSide) '' Set.Ici initial =
        {MapAt[i] EndAt[i,fresh,m,length]} := by
  dsimp only
  obtain ⟨tailSide, endpoint⟩ := K.exists_compatibleMeshCurrentRootwardEnd_terminal_bank compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  let initial : ℝ≥0 := ⟨R.terminalTime level RootAt[SourceAt[i],by omega],
    (R.terminalTime_pos level higher _).le⟩
  let tail := K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W
    CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] RootAt[SourceAt[i],by omega] tailSide
  let stem := K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W r side i fresh m length
  refine ⟨tailSide, pathRayExtension stem tail initial,
    continuous_pathRayExtension stem tail initial endpoint,
    pathRayExtension_path stem tail initial,
    pathRayExtension_tail stem tail initial endpoint, ?_,
    isClosed_pathRayExtension_range stem tail initial endpoint,
    isPathConnected_pathRayExtension_range stem tail initial endpoint, ?_⟩
  · exact (pathRayExtension_range stem tail initial endpoint).trans
      (congrArg (fun s => s ∪ tail '' Set.Ici initial)
        (K.compatibleMeshCurrentRootwardIntrinsicPath_range compact nonempty R no_boundary level
          higher M positive inner_disk beta acute W r side i fresh m length))
  · have separated (u : ℝ≥0) (after : initial < u) : tail u ∉ Set.range stem := by
      intro member
      have on_stem := (K.compatibleMeshCurrentRootwardIntrinsicPath_range compact nonempty R
        no_boundary level higher M positive inner_disk beta acute W r side i fresh m length).subset
        member
      obtain ⟨y, _, at_y⟩ := on_stem
      exact K.compatibleMeshProcessedWholeMap_ne_outer_terminalBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W FrontierAt[i] RootAt[SourceAt[i],by omega]
        tailSide u after y at_y
    have intersection := path_inter_dilation_ray stem tail initial endpoint separated
    rw [K.compatibleMeshCurrentRootwardIntrinsicPath_range] at intersection
    have at_end : tail initial = MapAt[i] EndAt[i,fresh,m,length] := endpoint.symm
    exact intersection.trans (congrArg Set.singleton at_end)

end Unfoldings.ConvexRoof
