module

public import Unfoldings.Roof.CompatibleRootwardComparisonRimChain
public import Unfoldings.Roof.CompatibleComparisonPhysicalCompletion

/-! Physical completions retain actual complete rootward-chain copies, fans and real rolls. -/

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

local instance rootwardPhysicalCompletionChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardPhysicalCompletionChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardPhysicalCompletionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "JunctionAt[" j "," h "," k "," hk "," L "," hl "]" =>
  K.compatibleMeshCurrentRootwardComparisonJunction compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk L hl
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "StemAt[" j "," h "," k "," hk "]" =>
  K.compatibleMeshCurrentRootwardIntrinsicPath compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W r side j h k hk
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

local notation "NewConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewHigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "NewRoofAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
  NewConformingAt[S,L,h]
  (K.compatible_section_interior compact nonempty R L NewHigherAt[L,h] M)

variable {φ : ℝ} {region : Set Plane}

open Classical in
local instance rootwardPhysicalCompletionFineFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations) : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

local notation "CompletedMapAt[" S "," L "," h "," e "]" =>
  K.compatibleMeshProcessedComparisonCompletedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h e

open Classical in
/-- Construct the complete actual physical refinement through the new rim. Its
whole original cut carrier, all original one-sided fan angles and every real
rolling heading are retained; matching certificates are not premises. -/
theorem exists_compatibleMeshCurrentRootwardPhysicalCompletion
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[FrontierAt[i],later,ordered]).CompletionMesh φ region
      (NewRoofAt[FrontierAt[i],later,ordered]).originalEdgeEquations) :
    let root := RootAt[SourceAt[i],by omega]
    let duration := R.terminalTime later root - R.terminalTime level root
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher root).le⟩
    ∃ tailSide : Bool, ∃ n : ℕ,
      ∃ coarse : ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundarySystem
          NewRetainAt[FrontierAt[i],later,ordered]).Chain n,
        ∃ physical : E.OriginalChainRefinement NewRetainAt[FrontierAt[i],later,ordered] coarse,
          CompletedMapAt[FrontierAt[i],later,ordered,E] ''
              E.originalComplex.boundaryChainTrace physical.chain =
            MapAt[FrontierAt[i]] '' (T).pairedComplex.boundaryChainTrace
                (ChainAt[i,fresh,m,length]) ∪
              Set.range (fun u : Set.Icc (0 : ℝ) duration =>
                K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
                  IncludedAt[FrontierAt[i]] root tailSide
                  (offsetNonnegativeIccParameter initial u)) ∧
          (∀ j, E.originalComplex.totalAngle
            (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
            (E.originalComplex.boundaryEndVertex
              (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
              (physical.chain.point (physical.coarseIndex j))) =
            (NewAt[FrontierAt[i],later,ordered]).pairedComplex.totalAngle
              NewRetainAt[FrontierAt[i],later,ordered]
              ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
                NewRetainAt[FrontierAt[i],later,ordered] (coarse.point j))) ∧
          Set.range (E.originalComplex.boundaryChainRollHeading physical.chain) =
            Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainRollHeading
              coarse) ∧
          (E.partition.pairedFolding.restrictFaces E.originalPieceSet).boundaryPosition
            (E.originalComplex.boundaryTurn
              (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
              physical.chain.last) =
            SpatialEnvelope.point M.plane (R.terminalPoint later root) := by
  dsimp only
  obtain ⟨tailSide, _, n, coarse, _, _, spatial, below, carrier⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonRimChain compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length later ordered
  let physical := K.compatibleMeshProcessedComparisonPhysicalRefinement compact nonempty R
    no_boundary
    level higher M positive inner_disk beta acute FrontierAt[i] later ordered E coarse below
  have trace := K.compatibleMeshProcessedComparisonPhysicalRefinement_whole_trace compact nonempty
    R
    no_boundary level higher M positive inner_disk beta acute W FrontierAt[i] later ordered E
    coarse below
  refine ⟨tailSide, n, coarse, physical, trace.trans carrier, ?_, physical.heading_range_eq, ?_⟩
  · exact fun j => physical.coarseIndex_totalAngle j
  · exact (E.originalMetricEquiv_toSpace NewRetainAt[FrontierAt[i],later,ordered]
      (E.originalComplex.vertexPoint (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
        (E.originalComplex.boundaryEndVertex
              (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
          (E.originalComplex.boundaryTurn
              (E.originalRetain NewRetainAt[FrontierAt[i],later,ordered])
            physical.chain.last)))).trans
      ((congrArg ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered]) physical.last_image).trans spatial)

end Unfoldings.ConvexRoof
