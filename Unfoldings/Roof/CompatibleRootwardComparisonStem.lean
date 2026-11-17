module

public import Unfoldings.Roof.CompatibleRootwardComparisonTerminalChain
public import Unfoldings.Roof.CompatibleRootwardIntrinsicPath
public import Unfoldings.Roof.CompatibleProcessedComparisonPaths
public import Unfoldings.Topology.PathFiberEndpoint

/-! Preserve the entire original rootward stem and its intrinsic endpoint in larger windows. -/

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

local instance rootwardComparisonStemChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonStemChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardComparisonStemNewFintype (S : (Fcut).parents.ParentFrontier)
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

/-- Every original current stem point stays below the original comparison truncation. -/
theorem compatibleMeshCurrentRootwardIntrinsicPath_height_le
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2) (u : unitInterval) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[FrontierAt[i]]
        (StemAt[i,fresh,m,length] u)).val) ≤ level := by
  have member := (K.compatibleMeshCurrentRootwardIntrinsicPath_range compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W r side i fresh m length).subset ⟨u, rfl⟩
  obtain ⟨x, _, at_x⟩ := member
  rw [← at_x, K.restore_compatibleMeshProcessedWholeMap]
  have in_clip := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[FrontierAt[i]] x
  rwa [M.clip_eq_sublevel, neg_neg] at in_clip

open Classical in
/-- Lift the whole original stem into any strictly larger comparison window, ending at
the same named junction. All original points and their entire carrier are preserved. -/
theorem exists_compatibleMeshCurrentRootwardComparisonStem
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    ∃ start : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Realization
        NewRetainAt[FrontierAt[i],later,ordered],
      ∃ P : Path start JunctionAt[i,fresh,m,length,later,ordered],
        (∀ u, K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
          higher M positive inner_disk beta acute W FrontierAt[i] later ordered (P u) =
            StemAt[i,fresh,m,length] u) ∧
        (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W FrontierAt[i] later ordered) '' Set.range P =
            MapAt[FrontierAt[i]] '' (T).pairedComplex.boundaryChainTrace
              (ChainAt[i,fresh,m,length]) := by
  let stem := StemAt[i,fresh,m,length]
  have below (u : unitInterval) :=
    (K.compatibleMeshCurrentRootwardIntrinsicPath_height_le compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length u).trans_lt ordered
  let lifted := K.compatibleMeshProcessedComparisonPathLift compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W FrontierAt[i] later ordered stem below
  have junction_below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered]
        JunctionAt[i,fresh,m,length,later,ordered])) < later := by
    rw [K.fold_compatibleMeshCurrentRootwardComparisonJunction,
      SpatialEnvelope.horizontal_point, R.terminalPoint_level level higher]
    exact ordered
  have endpoint := K.compatibleMeshProcessedComparisonWholeMap_rootwardJunction compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W r side i fresh m length later
    ordered
  have unique (z : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Realization
      NewRetainAt[FrontierAt[i],later,ordered])
      (same : K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W FrontierAt[i] later ordered z =
          K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W FrontierAt[i] later ordered
              JunctionAt[i,fresh,m,length,later,ordered]) :
      z = JunctionAt[i,fresh,m,length,later,ordered] :=
    (K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered _ junction_below z
      same.symm).symm
  obtain ⟨P, same, carrier⟩ := exists_path_to_of_unique_fiber
    (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W FrontierAt[i] later ordered) stem lifted
    (K.compatibleMeshProcessedComparisonWholeMap_pathLift compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W FrontierAt[i] later ordered stem below)
    JunctionAt[i,fresh,m,length,later,ordered] endpoint unique
  exact ⟨_, P, same, carrier.trans
    (K.compatibleMeshCurrentRootwardIntrinsicPath_range compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side i fresh m length)⟩

end Unfoldings.ConvexRoof
