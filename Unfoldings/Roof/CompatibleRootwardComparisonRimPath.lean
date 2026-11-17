module

public import Unfoldings.Roof.CompatibleRootwardComparisonStem

/-! Join the whole original rootward stem and its actual terminal chain through the new rim. -/

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

local instance rootwardComparisonRimPathChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonRimPathChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardComparisonRimPathNewFintype (S : (Fcut).parents.ParentFrontier)
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

open Classical in
/-- In every larger comparison window, join the whole original rootward stem to its
constructed terminal chain through the new rim. The literal endpoint copies are joined,
and the whole-cut carrier is exactly the original stem and original closed outer bank. -/
theorem exists_compatibleMeshCurrentRootwardComparisonRimPath
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    let root := RootAt[SourceAt[i],by omega]
    let duration := R.terminalTime later root - R.terminalTime level root
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher root).le⟩
    ∃ tailSide : Bool,
      ∃ D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide,
        ∃ start : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.Realization
            NewRetainAt[FrontierAt[i],later,ordered],
          ∃ P : Path start
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
              NewRetainAt[FrontierAt[i],later,ordered]
              ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
                NewRetainAt[FrontierAt[i],later,ordered]
                ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
                  NewRetainAt[FrontierAt[i],later,ordered] D.chain.last))),
            (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
              higher M positive inner_disk beta acute W FrontierAt[i] later ordered) ''
              Set.range P =
              MapAt[FrontierAt[i]] '' (T).pairedComplex.boundaryChainTrace
                (ChainAt[i,fresh,m,length]) ∪
              Set.range (fun u : Set.Icc (0 : ℝ) duration =>
                K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
                  IncludedAt[FrontierAt[i]] root tailSide
                  (offsetNonnegativeIccParameter initial u)) := by
  dsimp only
  obtain ⟨tailSide, D, joined, tail_image⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonTerminalChain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length later ordered
  obtain ⟨start, stem, same, stem_image⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonStem compact nonempty R no_boundary level higher
      M positive inner_disk beta acute W r side i fresh m length later ordered
  let tail := (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTraversal D.chain
  obtain ⟨P, carrier⟩ := exists_path_joining_copy stem tail joined
  refine ⟨tailSide, D, start, P, ?_⟩
  rw [carrier, Set.image_union, stem_image]
  have tail_range := (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTraversal_range
    D.chain
  exact congrArg (fun s => MapAt[FrontierAt[i]] ''
      (T).pairedComplex.boundaryChainTrace (ChainAt[i,fresh,m,length]) ∪ s)
    ((congrArg (Set.image (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W FrontierAt[i] later ordered))
        tail_range).trans tail_image)

end Unfoldings.ConvexRoof
