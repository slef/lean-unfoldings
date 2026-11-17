module

public import Unfoldings.Roof.CompatibleComparisonTerminalCompletion
public import Unfoldings.Roof.CompatibleProcessedTerminalMatching
public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Metric.PositiveClosedInterval

/-! Match entire actual directed comparison banks to their original terminal copies. -/

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

local instance comparisonTerminalMatchingIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalMatchingNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalMatchingWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Actual forward geometric endpoints determine one original whole-cut bank for every
point of a directed fine bank, including both endpoint copies. -/
theorem compatibleMeshProcessedComparison_directedBank_wholeTerminal
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots})
    (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
    {s t : ℝ} (after : R.terminalTime level r ≤ s) (forward : s < t)
    (first : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) s)
    (last : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) =
        R.exterior.ray (R.terminalIndex r) t) :
    ∃ side : Bool, ∀ u : unitInterval,
      K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered
        ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u) =
          OriginalAt[S,r,side]
            (nonnegativeIntervalLineMap s t
              ((R.terminalTime_pos level higher r).le.trans after) forward.le u) := by
  let time := nonnegativeIntervalLineMap s t
    ((R.terminalTime_pos level higher r).le.trans after) forward.le
  apply K.compatibleMeshProcessed_terminalBank_side_of_dense_after compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S r
    (fun u : unitInterval => K.compatibleMeshProcessedComparisonWholeMap compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u))
    ((K.compatibleMeshProcessedComparisonWholeMap_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered).continuous.comp
        ((NewAt[S,later,ordered]).pairedComplex.continuous_directedBoundaryPath p))
    time (continuous_nonnegativeIntervalLineMap _ _ _ _)
    {u | 0 < u.val} (isPreconnected_positiveIcc 1) (dense_positiveIcc zero_lt_one)
  · intro u hu
    change R.terminalTime level r < s + u.val * (t - s)
    exact after.trans_lt (lt_add_of_pos_right s (mul_pos hu (sub_pos.mpr forward)))
  · intro u
    have physical := congrArg Cap.horizontal
      (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered
          ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u))
    apply physical.trans
    apply ((NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath p u).trans
    rw [first, last]
    dsimp only [time, nonnegativeIntervalLineMap, SlopeEnvelope.ExteriorPlan.ray]
    rw [AffineMap.lineMap_apply_module']
    module

open Classical in
/-- A forward fine bank agrees with its whole completed comparison-bank restriction.
Continuity retains the new rim endpoint, where interior fiber uniqueness is unavailable. -/
theorem compatibleMeshProcessedComparison_directedBank_terminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots})
    (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
    (s t : Set.Icc (0 : ℝ) DurationAt[later,r]) (forward : s.val < t.val)
    (first : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) =
      R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + s.val))
    (last : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) =
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + t.val)) :
    ∃ side : Bool, ∀ u : unitInterval,
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
        FullBankAt[S,later,ordered,r,side]
          (closedNonnegativeIntervalLineMap s.val t.val DurationAt[later,r]
            s.property.1 forward.le t.property.2 u) := by
  let param := closedNonnegativeIntervalLineMap s.val t.val DurationAt[later,r]
    s.property.1 forward.le t.property.2
  let time := nonnegativeIntervalLineMap (R.terminalTime level r + s.val)
    (R.terminalTime level r + t.val)
    (by linarith [(R.terminalTime_pos level higher r), s.property.1])
    (by linarith)
  obtain ⟨side, matching⟩ :=
    K.compatibleMeshProcessedComparison_directedBank_wholeTerminal compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r p
      (le_add_of_nonneg_right s.property.1) (by linarith) first last
  have time_eq (u : unitInterval) :
      time u = offsetNonnegativeIccParameter StartAt[r] (param u) := by
    apply Subtype.ext
    change _ + s.val + u.val * (_ + t.val - (_ + s.val)) =
      _ + (s.val + u.val * (t.val - s.val))
    ring
  let target (u : unitInterval) := FullBankAt[S,later,ordered,r,side] (param u)
  have continuous_target : Continuous target :=
    (K.compatibleMeshProcessedComparisonTerminalClosedBank_lipschitz compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side).continuous.comp
      (continuous_closedNonnegativeIntervalLineMap _ _ _ _ _ _)
  have agrees : Set.EqOn
      ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p) target
        {u : unitInterval | u.val < 1} := by
    intro u hu
    have before : (time u).val < R.terminalTime later r := by
      change _ + s.val + u.val * (_ + t.val - (_ + s.val)) < _
      nlinarith [t.property.2, mul_pos (sub_pos.mpr hu) (sub_pos.mpr forward)]
    have physical := (congrArg (fun z => Cap.horizontal
      (W.partition.restoreCut CutsAt[S] z).val) (matching u)).trans
      ((congrArg Cap.horizontal (K.restore_restoredWholeTerminalBank compact nonempty R no_boundary
        W CutsAt[S] IncludedAt[S] r side (time u))).trans (SpatialEnvelope.horizontal_point _ _))
    have position := (congrArg Cap.horizontal
      (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered _)).symm.trans physical
    have below : (K.clippedExtension slopes compact nonempty).height
        (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
          NewRetainAt[S,later,ordered]
          ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u))) < later :=
      (congrArg (K.clippedExtension slopes compact nonempty).height position).trans_lt
        ((R.terminal_ray_below_iff later HigherAt[later,ordered] r (time u).property).mpr before)
    apply (VAt[later,ordered]).partialPairedMeshMap_injective_at ProperAt[later,ordered]
      FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights
      CutsAt[S]
      ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
      NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] _
      (by apply SpatialEnvelope.levelEquation_positive; rw [M.height_eq]; linarith) (target u)
    exact (matching u).trans
      ((congrArg OriginalAt[S,r,side] (time_eq u)).trans
        (K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R
          no_boundary level higher M positive inner_disk beta acute W S later ordered r side
            (param u)).symm)
  exact ⟨side, fun u => agrees.closure
    ((NewAt[S,later,ordered]).pairedComplex.continuous_directedBoundaryPath p)
      continuous_target (dense_intervalBelowEnd zero_lt_one u)⟩

end Unfoldings.ConvexRoof
