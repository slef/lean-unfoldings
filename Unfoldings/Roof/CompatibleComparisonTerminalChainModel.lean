module

public import Unfoldings.Roof.CompatibleComparisonTerminalChains
public import Unfoldings.Complex.BoundaryChainIntervalParameters
public import Unfoldings.Roof.SpatialEnvelopeTerminalVectors
public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.PolygonalLength

/-! Exact original time partitions and spatial vectors of constructed comparison bank chains. -/

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

local instance comparisonTerminalChainModelIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalChainModelNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalChainModelWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

open Classical in
/-- The constructed actual terminal chain together with all original time intervals.
Its fields record consequences of the construction, rather than input certificates. -/
structure CompatibleComparisonTerminalChainModel
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) where
  length : ℕ
  chain : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
    NewRetainAt[S,later,ordered]).Chain length
  lower : Fin (length + 1) → Set.Icc (0 : ℝ) DurationAt[later,r]
  upper : Fin (length + 1) → Set.Icc (0 : ℝ) DurationAt[later,r]
  forward : ∀ i, (lower i).val < (upper i).val
  first : ∀ i, Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
    (chain.point i)) = R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + (lower i).val)
  last : ∀ i, Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
    ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
      (chain.point i))) =
    R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + (upper i).val)
  matching : ∀ i u, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (chain.point i) u =
    FullBankAt[S,later,ordered,r,side]
      (closedNonnegativeIntervalLineMap (lower i).val (upper i).val DurationAt[later,r]
        (lower i).property.1 (forward i).le (upper i).property.2 u)
  trace : Set.range FullBankAt[S,later,ordered,r,side] =
    (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace chain
  start_time : (lower 0).val = 0
  finish_time : (upper (Fin.last length)).val = DurationAt[later,r]

open Classical in
/-- Construct the actual chain and its original time partition from the compatible cuts.
No chain, ordered intervals, edge-copy matched_paths or endpoint certificates are supplied. -/
def compatibleMeshProcessedComparisonTerminalChainModel
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered r side := by
  apply Classical.choice
  obtain ⟨n, chain, index, named, trace, initial, terminal⟩ :=
    K.exists_compatibleMeshProcessedComparisonTerminalBank_chain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side
  have choices (i : Fin (n + 1)) := (index i).property
  choose lower upper forward first last matching using choices
  have matched_paths : ∀ i u,
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (chain.point i) u =
        FullBankAt[S,later,ordered,r,side]
          (closedNonnegativeIntervalLineMap (lower i).val (upper i).val DurationAt[later,r]
            (lower i).property.1 (forward i).le (upper i).property.2 u) := by
    intro i u
    rw [named i]
    exact matching i u
  have embedded := K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W S later ordered r side
  refine ⟨⟨n, chain, lower, upper, forward, ?_, ?_, matched_paths, trace, ?_, ?_⟩⟩
  · intro i
    rw [named i]
    exact first i
  · intro i
    rw [named i]
    exact last i
  · exact congrArg Subtype.val (embedded.injective
      (((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_first chain lower upper
        forward FullBankAt[S,later,ordered,r,side] matched_paths 0).symm.trans initial))
  · exact congrArg Subtype.val (embedded.injective
      (((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_last chain lower upper
        forward FullBankAt[S,later,ordered,r,side] matched_paths (Fin.last n)).symm.trans terminal))

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {r : {v // v ∈ R.parents.roots}} {side : Bool}
  (D : K.CompatibleComparisonTerminalChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered r side)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}

open Classical in
/-- Adjacent actual terminal banks share one literal original time parameter. -/
theorem CompatibleComparisonTerminalChainModel.joins (i : Fin D.length) :
    D.upper i.castSucc = D.lower i.succ :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_joins D.chain D.lower D.upper
    D.forward FullBankAt[S,later,ordered,r,side]
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side).injective
    D.matching i

open Classical in
/-- The actual terminal chain moves strictly forward in original time. -/
theorem CompatibleComparisonTerminalChainModel.strictMono : StrictMono (fun i => (D.lower i).val) :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_strictMono D.chain D.lower D.upper
    D.forward FullBankAt[S,later,ordered,r,side] D.matching
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side).injective

open Classical in
/-- Every internal fine hinge is strictly past the old rim and strictly before the new rim. -/
theorem CompatibleComparisonTerminalChainModel.internal (i : Fin D.length) :
    0 < (D.lower i.succ).val ∧ (D.lower i.succ).val < DurationAt[later,r] :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_internal D.chain D.lower D.upper
    D.forward FullBankAt[S,later,ordered,r,side] D.matching
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side).injective
    i

open Classical in
/-- Actual chain vertices retain their literal original bank copies at the recorded times. -/
theorem CompatibleComparisonTerminalChainModel.vertexPoint (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        (D.chain.point i)) = FullBankAt[S,later,ordered,r,side] (D.lower i) :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_first D.chain D.lower D.upper
    D.forward FullBankAt[S,later,ordered,r,side] D.matching i

open Classical in
/-- Every actual forward fine edge keeps its original full spatial terminal velocity. -/
theorem CompatibleComparisonTerminalChainModel.spatialVector (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedFolding.germDirection (D.chain.point i).val =
      ((D.upper i).val - (D.lower i).val) • R.exterior.spatialDirection (R.terminalIndex r) := by
  have vector := (NewAt[S,later,ordered]).toTriangulation.germDirection_eq_terminal_spatialDirection
    R.exterior M (R.terminalIndex r) (D.chain.point i)
    (show 0 ≤ R.terminalTime level r + (D.lower i).val from
      add_nonneg (R.terminalTime_pos level higher r).le (D.lower i).property.1)
    (show 0 ≤ R.terminalTime level r + (D.upper i).val from
      add_nonneg (R.terminalTime_pos level higher r).le (D.upper i).property.1)
    (D.first i) (D.last i)
  simpa only [add_sub_add_left_eq_sub] using vector

open Classical in
/-- Each intrinsic fine-edge length is its original time increment times spatial speed. -/
theorem CompatibleComparisonTerminalChainModel.bankLength (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryBankLength (D.chain.point i) =
      ((D.upper i).val - (D.lower i).val) * ‖R.exterior.spatialDirection (R.terminalIndex r)‖ := by
  rw [(NewAt[S,later,ordered]).pairedFolding.boundaryBankLength_eq_germDirection_norm,
    D.spatialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (D.forward i).le)]

open Classical in
/-- The complete original time interval is partitioned without omissions or repetitions. -/
theorem CompatibleComparisonTerminalChainModel.sum_time :
    (∑ i, ((D.upper i).val - (D.lower i).val)) = DurationAt[later,r] := by
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun i : Fin (D.length + 1) => (D.upper i).val),
    Fin.sum_univ_succ (fun i : Fin (D.length + 1) => (D.lower i).val)]
  have same : (∑ i : Fin D.length, (D.upper i.castSucc).val) =
      ∑ i : Fin D.length, (D.lower i.succ).val :=
    Finset.sum_congr rfl (fun i _ => congrArg Subtype.val (D.joins i))
  rw [same, D.finish_time, D.start_time]
  ring

open Classical in
/-- Rolling the entire actual fine terminal chain preserves its full intrinsic arclength. -/
theorem CompatibleComparisonTerminalChainModel.rolledLength :
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).projectedLength =
      DurationAt[later,r] * ‖R.exterior.spatialDirection (R.terminalIndex r)‖ := by
  simp only [PolygonalChain.projectedLength,
    TriangleComplex.boundaryChainRoll_edge_length, D.bankLength, ← Finset.sum_mul, D.sum_time]

end Unfoldings.ConvexRoof
