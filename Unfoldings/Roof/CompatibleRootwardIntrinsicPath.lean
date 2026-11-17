module

public import Unfoldings.Roof.CompatibleRootwardTerminalJoin
public import Unfoldings.Roof.CompatibleProcessedTerminalBanks
public import Unfoldings.Complex.BoundaryChainPath
public import Unfoldings.Metric.DilationIntervalPath

/-! Continuous intrinsic rootward bank paths with arbitrary original terminal continuations. -/

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

local instance rootwardIntrinsicPathIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardIntrinsicPathWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Traverse the actual current rootward bank continuously in its intermediate whole cut,
retaining each original cut-vertex copy and the final actual intrinsic endpoint. -/
def compatibleMeshCurrentRootwardIntrinsicPath
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    Path (MapAt[i] StartAt[i,fresh,m,length]) (MapAt[i] EndAt[i,fresh,m,length]) :=
  (T).pairedComplex.mappedBoundaryChainTraversal (ChainAt[i,fresh,m,length]) MapAt[i]
    (K.compatibleMeshProcessedWholeMap_lipschitz compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i]).continuous

/-- The actual continuous intrinsic traversal retains exactly the original entire bank trace. -/
theorem compatibleMeshCurrentRootwardIntrinsicPath_range
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) :
    Set.range (K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length) =
        MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) := by
  exact (T).pairedComplex.mappedBoundaryChainTraversal_range
    (ChainAt[i,fresh,m,length]) MapAt[i] _

/-- Construct a continuous actual intrinsic bank path with any finite original terminal
continuation. Its carrier is exactly the original entire current stem and the original
closed terminal-bank interval, with the actual joined endpoint retained. -/
theorem exists_compatibleMeshCurrentRootward_terminal_path
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (time : ℝ≥0) :
    let root := RootAt[SourceAt[i],by omega]
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher _).le⟩
    ∃ tailSide : Bool, ∃ P : Path (MapAt[i] StartAt[i,fresh,m,length])
      (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
        IncludedAt[FrontierAt[i]] root tailSide (initial + time)),
      Set.range P = MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) ∪
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
          IncludedAt[FrontierAt[i]] root tailSide) '' Set.Icc initial (initial + time) ∧
      (MapAt[i] '' (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length])) ∩
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
          IncludedAt[FrontierAt[i]] root tailSide) '' Set.Icc initial (initial + time) =
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
  have ordered : initial ≤ initial + time := le_add_of_nonneg_right time.property
  refine ⟨tailSide, appendDilationPath tail initial (initial + time) ordered stem endpoint, ?_, ?_⟩
  · exact (appendDilationPath_range tail initial (initial + time) ordered stem endpoint).trans
      (congrArg (fun s => s ∪ tail '' Set.Icc initial (initial + time))
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
    have intersection := path_inter_dilation_interval tail initial (initial + time) ordered stem
      endpoint separated
    rw [K.compatibleMeshCurrentRootwardIntrinsicPath_range] at intersection
    have at_end : tail initial = MapAt[i] EndAt[i,fresh,m,length] := endpoint.symm
    exact intersection.trans (congrArg Set.singleton at_end)

end Unfoldings.ConvexRoof
