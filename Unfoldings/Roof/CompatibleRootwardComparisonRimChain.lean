module

public import Unfoldings.Roof.CompatibleRootwardComparisonChain
public import Unfoldings.Roof.CompatibleRootwardComparisonTerminalChain
public import Unfoldings.Roof.CompatibleComparisonTerminalStemJoins

/-! Complete actual rootward comparison chains retain the original stem and closed outer bank. -/

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

local instance rootwardComparisonRimChainChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardComparisonRimChainChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardComparisonRimChainNewFintype (S : (Fcut).parents.ParentFrontier)
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
/-- Construct the complete actual rootward chain through the new rim. Height
separates stem and terminal banks; their literal junction derives the successor.
The full original closed carrier and both endpoint copies survive. -/
theorem exists_compatibleMeshCurrentRootwardComparisonRimChain
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    let root := RootAt[SourceAt[i],by omega]
    let duration := R.terminalTime later root - R.terminalTime level root
    let initial : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher root).le⟩
    ∃ tailSide : Bool,
      ∃ D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W FrontierAt[i] later ordered root tailSide,
        ∃ n : ℕ, ∃ full : ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundarySystem
            NewRetainAt[FrontierAt[i],later,ordered]).Chain n,
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
            NewRetainAt[FrontierAt[i],later,ordered]
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
              NewRetainAt[FrontierAt[i],later,ordered] full.first) =
            LiftAt[FrontierAt[i],later,ordered,(ChainAt[i,fresh,m,length]).first] 0 ∧
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
            NewRetainAt[FrontierAt[i],later,ordered]
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
              NewRetainAt[FrontierAt[i],later,ordered]
              ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
                NewRetainAt[FrontierAt[i],later,ordered] full.last)) =
            (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
              NewRetainAt[FrontierAt[i],later,ordered]
              ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
                NewRetainAt[FrontierAt[i],later,ordered]
                ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
                  NewRetainAt[FrontierAt[i],later,ordered] D.chain.last)) ∧
          (NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
            ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
              NewRetainAt[FrontierAt[i],later,ordered] full.last) =
            SpatialEnvelope.point M.plane (R.terminalPoint later root) ∧
          (∀ j, (K.clippedExtension slopes compact nonempty).height
            (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
              (full.point j))) < later) ∧
          NewMapAt[FrontierAt[i],later,ordered] ''
            (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace full =
            MapAt[FrontierAt[i]] '' (T).pairedComplex.boundaryChainTrace
                (ChainAt[i,fresh,m,length]) ∪
              Set.range (fun u : Set.Icc (0 : ℝ) duration =>
                K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[FrontierAt[i]]
                  IncludedAt[FrontierAt[i]] root tailSide
                  (offsetNonnegativeIccParameter initial u)) := by
  dsimp only
  let root := RootAt[SourceAt[i],by omega]
  obtain ⟨a, stem, stem_first, stem_last, stem_image⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonChain compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W r side i fresh m length later ordered
  obtain ⟨tailSide, D, tail_first, tail_image⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonTerminalChain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length later ordered
  have below (x) (member : x ∈
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace stem) :=
    K.compatibleMeshProcessedComparison_height_le_of_original_image compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W FrontierAt[i] later ordered x (by
        obtain ⟨y, _, at_y⟩ := stem_image.subset ⟨x, member, rfl⟩
        exact ⟨y, at_y⟩)
  have endpoint := stem_last.trans tail_first.symm
  have apart := comparison_stem_terminal_chains_separated (D := D) stem below
  have joined := comparison_stem_terminal_chains_joined (D := D) stem below endpoint
  let full := stem.concat D.chain apart joined
  have first_name : full.first = stem.first := stem.concat_first D.chain apart joined
  have last_name : full.last = D.chain.last := stem.concat_last D.chain apart joined
  have first_copy := (congrArg (fun p =>
    (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
      NewRetainAt[FrontierAt[i],later,ordered]
      ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
        NewRetainAt[FrontierAt[i],later,ordered] p)) first_name).trans stem_first
  have last_copy := congrArg (fun p =>
    (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
      NewRetainAt[FrontierAt[i],later,ordered]
      ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
        NewRetainAt[FrontierAt[i],later,ordered]
        ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
          NewRetainAt[FrontierAt[i],later,ordered] p))) last_name
  have final_horizontal : Cap.horizontal
      ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
          NewRetainAt[FrontierAt[i],later,ordered] D.chain.last)) = R.terminalPoint later root := by
    apply (D.last (Fin.last D.length)).trans
    apply congrArg (R.exterior.ray (R.terminalIndex root))
    rw [D.finish_time]
    ring
  have final_spatial : (NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryTurn
        NewRetainAt[FrontierAt[i],later,ordered] full.last) =
      SpatialEnvelope.point M.plane (R.terminalPoint later root) := by
    rw [last_name]
    exact ((NewAt[FrontierAt[i],later,ordered]).toTriangulation.toSpace_eq_point
      NewRetainAt[FrontierAt[i],later,ordered] _).trans
      (congrArg (SpatialEnvelope.point M.plane) final_horizontal)
  have starts_below (k : Fin (a + D.length + 2)) :
      (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
          (full.point k))) < later := by
    rcases (stem.concat_point_range_iff D.chain apart joined (full.point k)).mp ⟨k, rfl⟩ with
      ⟨j, named⟩ | ⟨j, named⟩
    · have member : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.vertexPoint
          NewRetainAt[FrontierAt[i],later,ordered]
          ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryEndVertex
            NewRetainAt[FrontierAt[i],later,ordered] (stem.point j)) ∈
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace stem := by
        rw [(NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace_eq_union_paths]
        exact Set.mem_iUnion.mpr ⟨j, 0,
          (NewAt[FrontierAt[i],later,ordered]).pairedComplex.directedBoundaryPath_zero _⟩
      exact (congrArg (fun p => (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition p)))
        named).symm.trans_lt ((below _ member).trans_lt ordered)
    · have before : R.terminalTime level root + (D.lower j).val < R.terminalTime later root := by
        linarith [D.forward j, (D.upper j).property.2]
      have height_bound := (R.terminal_ray_below_iff later
        (fun v => (higher v).trans ordered) root
        (add_nonneg (R.terminalTime_pos level higher root).le (D.lower j).property.1)).mpr before
      have tail_below := (congrArg (K.clippedExtension slopes compact nonempty).height
        (D.first j)).trans_lt height_bound
      exact (congrArg (fun p => (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition p)))
        named).symm.trans_lt tail_below
  have trace : NewMapAt[FrontierAt[i],later,ordered] ''
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace full =
      NewMapAt[FrontierAt[i],later,ordered] ''
        (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace stem ∪
      NewMapAt[FrontierAt[i],later,ordered] ''
        (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace D.chain := by
    exact (congrArg (fun z => NewMapAt[FrontierAt[i],later,ordered] '' z)
      ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace_concat
        stem D.chain apart joined)).trans (Set.image_union _ _ _)
  exact ⟨tailSide, D, a + D.length + 1, full, first_copy, last_copy, final_spatial, starts_below,
    trace.trans (congrArg₂ (fun x y => x ∪ y) stem_image tail_image)⟩

end Unfoldings.ConvexRoof
