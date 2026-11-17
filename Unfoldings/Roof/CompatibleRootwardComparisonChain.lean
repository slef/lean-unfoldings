module

public import Unfoldings.Roof.CompatibleComparisonChainRefinement
public import Unfoldings.Roof.CompatibleRootwardComparisonStem
public import Unfoldings.Roof.CompatibleCompletionRootwardFans

/-! The entire actual rootward comparison chain ends at its literal terminal junction. -/

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

local instance rootwardComparisonChainChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonChainChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardComparisonChainNewFintype (S : (Fcut).parents.ParentFrontier)
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

open Classical in
/-- Construct the complete actual comparison chain of the original rootward stem.
Every original bank is refined in order, and the actual final vertex is the named
terminal junction. The entire original whole-cut carrier is unchanged. -/
theorem exists_compatibleMeshCurrentRootwardComparisonChain
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    ∃ n : ℕ, ∃ fine : ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundarySystem
        NewRetainAt[FrontierAt[i],later,ordered]).Chain n,
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[FrontierAt[i],later,ordered]
        ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
          NewRetainAt[FrontierAt[i],later,ordered] fine.first) =
        LiftAt[FrontierAt[i],later,ordered,(ChainAt[i,fresh,m,length]).first] 0 ∧
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
        NewRetainAt[FrontierAt[i],later,ordered]
        ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
          NewRetainAt[FrontierAt[i],later,ordered]
          ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
            NewRetainAt[FrontierAt[i],later,ordered] fine.last)) =
        JunctionAt[i,fresh,m,length,later,ordered] ∧
      NewMapAt[FrontierAt[i],later,ordered] ''
        (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace fine =
        MapAt[FrontierAt[i]] '' (T).pairedComplex.boundaryChainTrace
          (ChainAt[i,fresh,m,length]) := by
  have cut (j : Fin (m + 1)) :=
    K.compatibleMeshProcessed_boundaryEnd_is_cut_of_height_lt compact nonempty R no_boundary level
      higher M positive inner_disk beta acute FrontierAt[i] ((ChainAt[i,fresh,m,length]).point j)
      (K.compatibleMeshCurrentRootwardChain_corner_height_lt compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W r side i fresh m length j)
  obtain ⟨n, fine, first, last, trace⟩ :=
    K.exists_compatibleMeshProcessedComparison_chain_refinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered
      (ChainAt[i,fresh,m,length]) cut
  have last_map := (congrArg NewMapAt[FrontierAt[i],later,ordered] last).trans
    (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered
      (ChainAt[i,fresh,m,length]).last 1)
  rw [(T).pairedComplex.directedBoundaryPath_one] at last_map
  have junction_map := K.compatibleMeshProcessedComparisonWholeMap_rootwardJunction compact
    nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side i fresh m length later
    ordered
  have junction_below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered]
        JunctionAt[i,fresh,m,length,later,ordered])) < later := by
    rw [K.fold_compatibleMeshCurrentRootwardComparisonJunction,
      SpatialEnvelope.horizontal_point, R.terminalPoint_level level higher]
    exact ordered
  have endpoint := K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W FrontierAt[i] later ordered _
    junction_below _ (junction_map.trans last_map.symm)
  exact ⟨n, fine, first, endpoint.symm, trace⟩

end Unfoldings.ConvexRoof
