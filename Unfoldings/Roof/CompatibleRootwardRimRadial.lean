module

public import Unfoldings.Roof.CompatibleRootwardRadialHeading
public import Unfoldings.Roof.CompatibleRootwardTerminalRadial
public import Unfoldings.Roof.CompatibleRootwardComparisonTerminalChain
public import Unfoldings.Roof.CompatibleComparisonTerminalStemJoins

/-! Complete actual rootward chains preserve radial margins through the new rim. -/

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

local instance rootwardRimRadialChainChartIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

variable (W : R.WholeCutModel M)

local instance rootwardRimRadialChainChartWholeFintype : Fintype W.Index := W.finiteIndex

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
local instance rootwardRimRadialChainNewFintype (S : (Fcut).parents.ParentFrontier)
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

variable {b : ℝ} (bpos : 0 < b) (ratio : a ≤ b) (upper : ∀ p ∈ slopes, ‖p‖ ≤ b)
  (small : 2 * annularHistoryAngle (a / b) β < Real.pi / 2)

include bpos ratio upper small

open Classical in
/-- Construct the complete actual rootward chain through the new rim. Height
separates stem and terminal banks; their literal junction derives the successor.
The full original closed carrier and both endpoint copies survive. -/
theorem exists_compatibleMeshCurrentRootwardComparisonRimRadialChain
    (i : Fin ((contour).length + 1)) (fresh : SourceAt[i] ∉ (FrontierAt[i]).processed)
    (m : ℕ) (length : (Fcut).parents.distanceToRoot SourceAt[i] = m + 2)
    (later : ℝ) (ordered : level < later) :
    let root := RootAt[SourceAt[i],by omega]
    let duration := R.terminalTime later root - R.terminalTime level root
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
          (∀ j, Real.cos (2 * annularHistoryAngle (a / b) β) *
            (‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
                (full.point j)) - (Q).projectedVertex SourceAt[i]‖ *
              ‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection
                (full.point j).val)‖) ≤
            inner ℝ (Cap.horizontal
              ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
              (full.point j)) - (Q).projectedVertex SourceAt[i])
              (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection
                (full.point j).val))) ∧
          ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
            full).RadialFrom
            ((Q).projectedVertex SourceAt[i]) 0 ∧
          0 < dist ((Q).projectedVertex SourceAt[i])
            (((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
              full).vertex 0) ∧
          Set.range
            ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain full).path =
            Set.range (PathAt[i,fresh,m,length]).path ∪
              Set.range (fun u : Set.Icc (0 : ℝ) duration =>
                R.exterior.ray (R.terminalIndex root) (R.terminalTime level root + u.val)) := by
  dsimp only
  let root := RootAt[SourceAt[i],by omega]
  obtain ⟨nStem, stem, stem_first, stem_last, stem_carrier, stem_margin, stem_radial,
      stem_initial, _stem_heading⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonRadialHeadingChain compact nonempty R
      no_boundary
      level higher M positive inner_disk beta acute W r side bpos ratio upper small
      i fresh m length later ordered
  obtain ⟨tailSide, D, tail_first, tail_image⟩ :=
    K.exists_compatibleMeshCurrentRootwardComparisonTerminalChain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W r side i fresh m length later ordered
  have below (x) (member : x ∈
      (NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace stem) :
      (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
          NewRetainAt[FrontierAt[i],later,ordered] x)) ≤ level := by
    have in_stem : Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered] x) ∈
        Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
          stem).path := by
      rw [SpatialFolding.projectedBoundaryChain_path_range]
      exact ⟨x, member, rfl⟩
    have in_old := stem_carrier.subset in_stem
    change Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
      NewRetainAt[FrontierAt[i],later,ordered] x) ∈
      Set.range ((T).pairedFolding.projectedBoundaryChain (ChainAt[i,fresh,m,length])).path
        at in_old
    rw [SpatialFolding.projectedBoundaryChain_path_range] at in_old
    obtain ⟨y, _, same⟩ := in_old
    have bound := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[FrontierAt[i]] y
    rw [M.clip_eq_sublevel, neg_neg] at bound
    exact (congrArg (K.clippedExtension slopes compact nonempty).height same.symm).trans_le bound
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
  have starts_below (k : Fin (nStem + D.length + 2)) :
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
  let test (p : (NewAt[FrontierAt[i],later,ordered]).pairedComplex.BoundaryEnd
      NewRetainAt[FrontierAt[i],later,ordered]) : Prop :=
    Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition p) -
          (Q).projectedVertex SourceAt[i]‖ *
        ‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection p.val)‖) ≤
      inner ℝ (Cap.horizontal
        ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition p) -
        (Q).projectedVertex SourceAt[i])
        (Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection p.val))
  have full_margin (j : Fin (nStem + D.length + 2)) : test (full.point j) := by
    rcases (stem.concat_point_range_iff D.chain apart joined (full.point j)).mp ⟨j, rfl⟩ with
      ⟨k, named⟩ | ⟨k, named⟩
    · exact Eq.mp (congrArg test named) (stem_margin k)
    · exact Eq.mp (congrArg test named)
        (K.compatibleMeshCurrentRootwardComparisonTerminal_radial_margin compact nonempty R
          no_boundary
          level higher M positive inner_disk beta acute W r side bpos ratio upper small
          i fresh m length later ordered tailSide D k)
  have radial : ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
      full).RadialFrom ((Q).projectedVertex SourceAt[i]) 0 := by
    intro j _
    apply (monotone_dist_lineMap_iff _ _ _).mpr
    have bound := full_margin j
    change Real.cos (2 * annularHistoryAngle (a / b) β) *
      (‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition
          (full.point j)) - (Q).projectedVertex SourceAt[i]‖ *
        ‖Cap.horizontal ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.germDirection
          (full.point j).val)‖) ≤ _ at bound
    rw [← (NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc
      full j, ←
        (NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain_edge full j]
      at bound
    exact (mul_nonneg (fine_annular_radial_margin_pos small).le
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans bound
  have first_projection :
      ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain full).vertex 0 =
        ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
          stem).vertex 0 := by
    exact ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc
      full 0).trans ((congrArg (fun p => Cap.horizontal
        ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.boundaryPosition p)) first_name).trans
          ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc
            stem 0).symm)
  have trace :
      Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
        full).path =
      Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
        stem).path ∪
      Set.range ((NewAt[FrontierAt[i],later,ordered]).pairedFolding.projectedBoundaryChain
        D.chain).path := by
    rw [SpatialFolding.projectedBoundaryChain_path_range,
      SpatialFolding.projectedBoundaryChain_path_range,
        SpatialFolding.projectedBoundaryChain_path_range]
    exact (congrArg (fun z => (Cap.horizontal ∘
      (NewAt[FrontierAt[i],later,ordered]).pairedFolding.toSpace
        NewRetainAt[FrontierAt[i],later,ordered])
        '' z) ((NewAt[FrontierAt[i],later,ordered]).pairedComplex.boundaryChainTrace_concat
          stem D.chain apart joined)).trans (Set.image_union _ _ _)
  exact ⟨tailSide, D, nStem + D.length + 1, full, first_copy, last_copy, final_spatial,
    starts_below,
    full_margin, radial,
    stem_initial.trans_eq (congrArg (dist ((Q).projectedVertex SourceAt[i])) first_projection).symm,
    trace.trans (congrArg₂ (fun x y => x ∪ y) stem_carrier D.projected_carrier)⟩

end Unfoldings.ConvexRoof
