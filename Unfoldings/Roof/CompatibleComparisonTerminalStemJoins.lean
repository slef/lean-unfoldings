module

public import Unfoldings.Roof.CompatibleComparisonTerminalChainModel
public import Unfoldings.Complex.BoundaryChainConcatenation

/-! Separate and join complete comparison stem and terminal chains by original roof height. -/

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

local instance comparisonTerminalStemJoinsIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

local notation "RetainAt[" S "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) S

local notation "CutsAt[" S "]" => K.compatibleMeshProcessedCarrier compact nonempty R no_boundary
  level higher M positive inner_disk beta acute S
local notation "PairsAt[" S "," L "]" => K.compatibleMeshProcessedWindowPairs compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S L

local notation "NewAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh compact nonempty R no_boundary level higher M positive
    inner_disk beta acute S L h
local notation "HigherAt[" _L "," h "]" => fun v => lt_trans (higher v) h
local notation "VAt[" L "," h "]" => R.levelWindowModel M L HigherAt[L,h]
local notation "ProperAt[" L "," h "]" => R.levelWindow_proper M L HigherAt[L,h]
local notation "FullAt[" L "," h "]" => R.levelWindow_full M L HigherAt[L,h]
local notation "DomainAt[" L "]" => SpatialEnvelope.levelEquation_domain M.plane (-L)
local notation "Heights" => Set.eqOn_refl (SpatialEnvelope.height M.plane) _
local notation "ClosedAt[" S "]" => K.isClosed_compatibleMeshProcessedCarrier compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "IncludedAt[" S "]" => K.compatibleMeshProcessedCarrier_subset compact nonempty R
  no_boundary level higher M positive inner_disk beta acute S
local notation "OutsideAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_cut_disjoint_interior compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S L h
local notation "ConformingAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S L h
local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RemovedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.removed_edge_mem_cut
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "RetainedAt[" S "," L "," h "]" =>
  SpatialEnvelope.Triangulation.retained_openSeamImage_disjoint
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S L h)

open Classical in
local instance comparisonTerminalStemJoinsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalStemJoinsWholeFintype : Fintype W.Index := W.finiteIndex

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later} {n : ℕ}
  {root : {v // v ∈ R.parents.roots}} {tailSide : Bool}
  (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered root tailSide)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}

open Classical in
/-- Original height separates every stem fine bank from every terminal fine bank,
including reversed orientations. Only the stem's derived original height bound is used. -/
theorem comparison_stem_terminal_chains_separated
    (stem : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (below : ∀ x ∈ (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace stem,
      (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
          NewRetainAt[S,later,ordered] x)) ≤ level) :
    ∀ (i : Fin (n + 1)) (j : Fin (D.length + 1)), stem.point i ≠ D.chain.point j ∧
      stem.point i ≠ (NewAt[S,later,ordered]).pairedComplex.boundaryTurn
        NewRetainAt[S,later,ordered] (D.chain.point j) := by
  intro i j
  have apart : ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
      NewRetainAt[S,later,ordered] (stem.point i)).1 ≠
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
        NewRetainAt[S,later,ordered] (D.chain.point j)).1 := by
    intro same_bank
    let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    let clock := closedNonnegativeIntervalLineMap (D.lower j).val (D.upper j).val
      (R.terminalTime later root - R.terminalTime level root)
      (D.lower j).property.1 (D.forward j).le (D.upper j).property.2 half
    have positive_clock : 0 < clock.val := by
      change 0 < (D.lower j).val + (1 / 2) * ((D.upper j).val - (D.lower j).val)
      linarith [(D.lower j).property.1, D.forward j]
    have member : (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath
        (D.chain.point j) half ∈
        Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (stem.point i)) := by
      rw [(NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_range, same_bank]
      exact ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_range
        (D.chain.point j)).subset ⟨half, rfl⟩
    have on_stem : (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath
        (D.chain.point j) half ∈
        (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace stem := by
      rw [(NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace_eq_union_paths]
      exact Set.mem_iUnion.mpr ⟨i, member⟩
    have spatial := (congrArg ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered]) (D.matching j half)).trans
      (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered root tailSide clock)
    have projected := (congrArg Cap.horizontal spatial).trans (SpatialEnvelope.horizontal_point _ _)
    have height_bound := (congrArg (K.clippedExtension slopes compact nonempty).height
      projected).symm.trans_le (below _ on_stem)
    have time_bound := (R.terminal_ray_sublevel_iff level higher root
      (add_nonneg (R.terminalTime_pos level higher root).le clock.property.1)).mp height_bound
    change R.terminalTime level root + clock.val ≤ R.terminalTime level root at time_bound
    linarith
  constructor
  · intro same
    exact apart (congrArg (fun p => ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
      NewRetainAt[S,later,ordered] p).1) same)
  · intro same
    have banks := congrArg (fun p => ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
      NewRetainAt[S,later,ordered] p).1) same
    exact apart (by
      simpa only [TriangleComplex.boundaryTurn, Equiv.apply_symm_apply] using! banks)

open Classical in
/-- The literal original junction and height separation determine the actual
successor between the completed stem and terminal chains. -/
theorem comparison_stem_terminal_chains_joined
    (stem : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (below : ∀ x ∈ (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace stem,
      (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
          NewRetainAt[S,later,ordered] x)) ≤ level)
    (endpoint : (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
            stem.last)) =
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
          D.chain.first)) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryMate NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        stem.last) = D.chain.first := by
  have vertices := (NewAt[S,later,ordered]).pairedComplex.vertexPoint_injective
    NewRetainAt[S,later,ordered] endpoint
  have distinct : D.chain.first ≠
      (NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        stem.last := by
    intro same
    have reversed := congrArg
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]) same
    rw [(NewAt[S,later,ordered]).pairedComplex.boundaryTurn_involutive] at reversed
    exact (comparison_stem_terminal_chains_separated (D := D) stem below
      (Fin.last n) 0).2 reversed.symm
  exact ((NewAt[S,later,ordered]).pairedComplex.exists_unique_other_boundaryEnd
    NewRetainAt[S,later,ordered]
    ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] stem.last)
    |>.unique ⟨distinct, vertices.symm⟩
      ((NewAt[S,later,ordered]).pairedComplex.boundaryMate_spec NewRetainAt[S,later,ordered] _)
    ).symm

end Unfoldings.ConvexRoof
