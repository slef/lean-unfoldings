module

public import Unfoldings.Roof.CompatibleComparisonTerminalCompletion
public import Unfoldings.Roof.CompatibleComparisonTerminalVertices
public import Unfoldings.Roof.CompatibleComparisonTerminalAlignment
public import Unfoldings.Roof.CompatibleComparisonTerminalMatching
public import Unfoldings.Topology.ClosedIntervalFiniteExceptions

/-! Cover each actual completed terminal bank by whole original forward fine banks. -/

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

local instance comparisonTerminalPiecesIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalPiecesNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalPiecesWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Opposite actual finite outer banks retain distinct copies strictly past the old rim. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_ne
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side other : Bool) (different : side ≠ other)
    (s t : Set.Icc (0 : ℝ) DurationAt[later,r]) (after : 0 < s.val) :
    FullBankAt[S,later,ordered,r,side] s ≠ FullBankAt[S,later,ordered,r,other] t := by
  intro same
  apply K.compatibleMeshProcessed_terminalBank_ne compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S r side other different
    (offsetNonnegativeIccParameter StartAt[r] s) (offsetNonnegativeIccParameter StartAt[r] t)
    (by change _ < _ + s.val; linarith)
  exact (K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered r side s).symm.trans
    ((congrArg (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered) same).trans
      (K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered r other t))

open Classical in
/-- A nonvertex contact occurs strictly past the old rim. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_time_pos_of_nonvertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : Set.Icc (0 : ℝ) DurationAt[later,r])
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      FullBankAt[S,later,ordered,r,side] t ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v) :
    0 < t.val := by
  by_contra not_positive
  have zero : t.val = 0 := le_antisymm (not_lt.mp not_positive) t.property.1
  obtain ⟨vertex, position⟩ :=
    K.exists_compatibleMeshProcessedComparisonTerminalClosedBank_endpoint_vertex compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side t
        (Or.inl zero)
  exact regular vertex position.symm

open Classical in
/-- A nonvertex point of the completed bank constructs an entire forward fine-bank
restriction of that same named side. Endpoint bounds and direction are derived. -/
theorem exists_forwardDirectedBank_at_compatibleMeshProcessedComparisonTerminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : Set.Icc (0 : ℝ) DurationAt[later,r])
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      FullBankAt[S,later,ordered,r,side] t ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v) :
    ∃ (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (s z : Set.Icc (0 : ℝ) DurationAt[later,r]) (forward : s.val < z.val),
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) =
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + s.val) ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) =
          R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + z.val) ∧
      (∃ u : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
        FullBankAt[S,later,ordered,r,side] t) ∧
      ∀ u : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
        FullBankAt[S,later,ordered,r,side]
          (closedNonnegativeIntervalLineMap s.val z.val DurationAt[later,r]
            s.property.1 forward.le z.property.2 u) := by
  obtain ⟨p, u, at_point⟩ :=
    (NewAt[S,later,ordered]).pairedComplex.exists_directedBoundaryPath_of_mem_boundary
      (K.compatibleMeshProcessedComparisonTerminalClosedBank_mem_boundary compact nonempty R
        no_boundary level higher M positive inner_disk beta acute W S later ordered r side t)
  have regular_p : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v :=
    fun v same => regular v (at_point.symm.trans same)
  have position := (congrArg (fun z => Cap.horizontal
    ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered] z)) at_point).trans
    ((congrArg Cap.horizontal
      (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered r side t)).trans
      (SpatialEnvelope.horizontal_point _ _))
  have member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
    rw [position]
    change R.exterior.ray (R.terminalIndex r) (_ + t.val) ∈
      segment ℝ (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r))
        (R.exterior.ray (R.terminalIndex r) (R.terminalTime later r))
    rw [← R.terminal_ray_interval r _ _ ((R.terminalTime_strictMono r) ordered).le]
    exact ⟨R.terminalTime level r + t.val, ⟨by linarith [t.property.1],
      by linarith [t.property.2]⟩, rfl⟩
  obtain ⟨q, s, z, forward, first, last, v, contact⟩ :=
    K.exists_compatibleMeshProcessedComparison_forward_terminal_bank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S later ordered r p u regular_p member
  obtain ⟨found_side, same⟩ :=
    K.compatibleMeshProcessedComparison_directedBank_terminalClosedBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r q s z
        forward first last
  have chosen_side : side = found_side := by
    by_contra different
    exact K.compatibleMeshProcessedComparisonTerminalClosedBank_ne compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side found_side different
      t _ (K.compatibleMeshProcessedComparisonTerminalClosedBank_time_pos_of_nonvertex compact
        nonempty R no_boundary level higher M positive inner_disk beta acute W S later ordered
          r side t regular) (at_point.symm.trans (contact.symm.trans (same v)))
  subst found_side
  exact ⟨q, s, z, forward, first, last, ⟨v, contact.trans at_point⟩, same⟩

open Classical in
/-- Whole forward fine banks that are exact subintervals of the chosen completed bank. -/
def compatibleMeshProcessedComparisonTerminalBankEnds
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set ((NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered]) :=
  {p | ∃ (s z : Set.Icc (0 : ℝ) DurationAt[later,r]) (forward : s.val < z.val),
    Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + s.val) ∧
    Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) =
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + z.val) ∧
    ∀ u : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
      FullBankAt[S,later,ordered,r,side]
        (closedNonnegativeIntervalLineMap s.val z.val DurationAt[later,r]
          s.property.1 forward.le z.property.2 u)}

open Classical in
/-- Whole forward fine banks cover the entire completed terminal bank, including every
subdivision vertex and both actual endpoint copies. -/
theorem compatibleMeshProcessedComparisonTerminalBank_range_eq_union_directedBanks
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set.range FullBankAt[S,later,ordered,r,side] =
      ⋃ p : K.compatibleMeshProcessedComparisonTerminalBankEnds compact nonempty R no_boundary level
          higher M positive inner_disk beta acute W S later ordered r side,
        Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p.val) := by
  let curve := FullBankAt[S,later,ordered,r,side]
  let ends := K.compatibleMeshProcessedComparisonTerminalBankEnds compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered r side
  let pieces := ⋃ p : ends,
    Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p.val)
  have closed : IsClosed pieces := isClosed_iUnion_of_finite
    (fun p : ends => (isCompact_range
      ((NewAt[S,later,ordered]).pairedComplex.continuous_directedBoundaryPath p.val)).isClosed)
  have embedded := K.compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W S later ordered r side
  have vertex_times : {t | curve t ∈ Set.range
      ((NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered])}.Finite :=
    Set.Finite.preimage embedded.injective.injOn (Set.finite_range _)
  have exceptions : {t | curve t ∉ pieces}.Finite := vertex_times.subset (by
    intro t missing
    by_contra regular
    have nonvertex :
        ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
          curve t ≠ (NewAt[S,later,ordered]).pairedComplex.vertexPoint
            NewRetainAt[S,later,ordered] v :=
      fun v same => regular ⟨v, same.symm⟩
    obtain ⟨p, s, z, forward, first, last, ⟨u, contact⟩, entire⟩ :=
      K.exists_forwardDirectedBank_at_compatibleMeshProcessedComparisonTerminalClosedBank compact
        nonempty R no_boundary level higher M positive inner_disk beta acute W S later ordered
          r side t nonvertex
    exact missing (Set.mem_iUnion.mpr
      ⟨⟨p, s, z, forward, first, last, entire⟩, u, contact⟩))
  have covered := continuous_Icc_mem_closed_of_finite_exceptions
    (sub_pos.mpr ((R.terminalTime_strictMono r) ordered)) curve
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_lipschitz compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side).continuous
    closed exceptions
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact covered t
  · intro x member
    obtain ⟨p, u, rfl⟩ := Set.mem_iUnion.mp member
    obtain ⟨s, z, forward, _, _, entire⟩ := p.property
    exact ⟨_, (entire u).symm⟩

end Unfoldings.ConvexRoof
