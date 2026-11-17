module

public import Unfoldings.Roof.CompatibleComparisonJunctionFan
public import Unfoldings.Roof.CompatibleComparisonTerminalChainModel
public import Unfoldings.Roof.CompatibleProcessedComparisonFiber
public import Unfoldings.Topology.ImageRange

/-! Join constructed outer terminal chains to the actual old rootward junction copies. -/

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

local instance rootwardComparisonTerminalChainChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonTerminalChainChartWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "ImageAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W FrontierAt[j]
    (K.compatibleMeshCurrentRootwardEnd compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W r side j h k hk)

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

open Classical in
local instance rootwardComparisonTerminalChainNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

open Classical in
/-- Construct an entire ordered terminal chain joined to the actual original rootward
junction. The original side and literal intrinsic start copy are derived, and every
original outer bank copy survives in its whole-cut image. -/
theorem exists_compatibleMeshCurrentRootwardComparisonTerminalChain
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    let root := RootAt[SourceAt[i],by omega]
    let duration := R.terminalTime later root - R.terminalTime level root
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher root).le⟩
    ∃ tailSide : Bool,
      ∃ D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide,
        (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
          NewRetainAt[FrontierAt[i],later,ordered]
          ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
            NewRetainAt[FrontierAt[i],later,ordered] D.chain.first) =
          JunctionAt[i,fresh,m,length,later,ordered] ∧
        (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W FrontierAt[i] later ordered) ''
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace D.chain =
            Set.range (fun u : Set.Icc (0 : ℝ) duration =>
              K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
                IncludedAt[FrontierAt[i]] root tailSide
                (offsetNonnegativeIccParameter initial u)) := by
  dsimp only
  let root := RootAt[SourceAt[i],by omega]
  let duration := R.terminalTime later root - R.terminalTime level root
  have duration_positive : 0 < duration := sub_pos.mpr ((R.terminalTime_strictMono root) ordered)
  let zero_time : Set.Icc (0 : ℝ) duration := ⟨0, le_rfl, duration_positive.le⟩
  obtain ⟨tailSide, endpoint⟩ := K.exists_compatibleMeshCurrentRootwardEnd_terminal_bank compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length
  let D := K.compatibleMeshProcessedComparisonTerminalChainModel compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide
  let bank := K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide
  have start_parameter : D.lower 0 = zero_time := Subtype.ext D.start_time
  have start_copy : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
      NewRetainAt[FrontierAt[i],later,ordered]
      ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
        NewRetainAt[FrontierAt[i],later,ordered] D.chain.first) = bank zero_time :=
    (D.vertexPoint 0).trans (congrArg bank start_parameter)
  have junction_below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered]
        JunctionAt[i,fresh,m,length,later,ordered])) < later := by
    rw [K.fold_compatibleMeshCurrentRootwardComparisonJunction,
      SpatialEnvelope.horizontal_point, R.terminalPoint_level level higher]
    exact ordered
  have junction_copy : JunctionAt[i,fresh,m,length,later,ordered] = bank zero_time := by
    apply K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W FrontierAt[i] later ordered _ junction_below _
    have original := (K.compatibleMeshProcessedComparisonWholeMap_rootwardJunction compact
      nonempty R no_boundary level higher M positive inner_disk beta acute W r side i fresh m length later
        ordered).trans endpoint
    apply original.trans
    apply Eq.symm
    have image := K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W FrontierAt[i] later ordered root
      tailSide zero_time
    apply image.trans
    apply congrArg (K.restoredWholeTerminalBank compact nonempty R no_boundary W
      CutsAt[FrontierAt[i]] IncludedAt[FrontierAt[i]] root tailSide)
    apply Subtype.ext
    exact add_zero _
  refine ⟨tailSide, D, start_copy.trans junction_copy.symm, ?_⟩
  rw [← D.trace]
  exact image_range_eq_of_pointwise _ bank _
    (K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide)

end Unfoldings.ConvexRoof
