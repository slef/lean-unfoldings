module

public import Unfoldings.Roof.CompatibleComparisonTerminalBoundary
public import Unfoldings.Roof.TerminalBands
public import Unfoldings.Metric.OffsetIntervalTime

/-! Complete original terminal banks at the rim of larger comparison meshes. -/

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

local instance comparisonTerminalCompletionIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalCompletionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalCompletionWholeFintype : Fintype W.Index := W.finiteIndex

local notation "StartAt[" r "]" =>
  (Subtype.mk (R.terminalTime level r) (le_of_lt (R.terminalTime_pos level higher r)) : ℝ≥0)
local notation "DurationAt[" L "," r "]" => R.terminalTime L r - R.terminalTime level r
local notation "OriginalAt[" S "," r "," side "]" =>
  K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S]
    IncludedAt[S] r side

/-- The original outer bank before the new rim, with its original time offset retained. -/
@[macro_inline] def compatibleMeshProcessedComparisonTerminalCurve
    (S : (Fcut).parents.ParentFrontier) (later : ℝ)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set.Ico (0 : ℝ) DurationAt[later,r] → W.partition.Cut CutsAt[S] :=
  OriginalAt[S,r,side] ∘ offsetNonnegativeIcoParameter StartAt[r]

local notation "CurveAt[" S "," L "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalCurve compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L r side

/-- The relative half-open parameter preserves the original bank's exact speed bound. -/
theorem compatibleMeshProcessedComparisonTerminalCurve_lipschitz
    (S : (Fcut).parents.ParentFrontier) (later : ℝ)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    LipschitzWith (Dilation.ratio OriginalAt[S,r,side]) CurveAt[S,later,r,side] :=
  dilation_comp_isometry_lipschitz OriginalAt[S,r,side] _
    (offsetNonnegativeIcoParameter_isometry StartAt[r])

/-- Every original pre-rim terminal point lies strictly inside the larger window. -/
theorem compatibleMeshProcessedComparisonTerminalCurve_positive
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Ico (0 : ℝ) DurationAt[later,r]) :
    ∀ j, 0 < SpatialEnvelope.levelEquation M.plane (-later) j
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (CurveAt[S,later,r,side] u)).val) := by
  have before : (offsetNonnegativeIcoParameter StartAt[r] u).val < R.terminalTime later r := by
    change R.terminalTime level r + u.val < R.terminalTime later r
    linarith [u.property.2]
  have below := K.compatibleMeshProcessed_terminal_below_comparison compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered r side
    (offsetNonnegativeIcoParameter StartAt[r] u) before
  change (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut CutsAt[S] (CurveAt[S,later,r,side] u)).val) < later
      at below
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

open Classical in
/-- Lift the entire pre-rim bank to its canonical actual finite copies. -/
def compatibleMeshProcessedComparisonTerminalLift
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set.Ico (0 : ℝ) DurationAt[later,r] →
      (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  (VAt[later,ordered]).partialPairedMeshCurveLift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Ico (0 : ℝ) DurationAt[later,r]) CurveAt[S,later,r,side]
    (K.compatibleMeshProcessedComparisonTerminalCurve_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side)

local notation "LiftAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalLift compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h r side

open Classical in
/-- The canonical pre-rim lift retains the original common Lipschitz constant. -/
theorem compatibleMeshProcessedComparisonTerminalLift_lipschitz
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    LipschitzWith (Dilation.ratio OriginalAt[S,r,side]) LiftAt[S,later,ordered,r,side] :=
  (VAt[later,ordered]).partialPairedMeshCurveLift_lipschitz ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Ico (0 : ℝ) DurationAt[later,r]) CurveAt[S,later,r,side]
    (K.compatibleMeshProcessedComparisonTerminalCurve_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side)
    (convex_Ico _ _)
    (K.compatibleMeshProcessedComparisonTerminalCurve_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later r side)

open Classical in
/-- The complete pre-rim lift keeps every original intrinsic bank copy. -/
theorem compatibleMeshProcessedComparisonWholeMap_terminalLift
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Ico (0 : ℝ) DurationAt[later,r]) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered (LiftAt[S,later,ordered,r,side] u) =
        OriginalAt[S,r,side] (offsetNonnegativeIcoParameter StartAt[r] u) :=
  (VAt[later,ordered]).partialPairedMeshMap_curveLift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Ico (0 : ℝ) DurationAt[later,r]) CurveAt[S,later,r,side]
    (K.compatibleMeshProcessedComparisonTerminalCurve_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side) u

open Classical in
/-- Complete the actual outer bank at its new original rim copy by the intrinsic metric. -/
def compatibleMeshProcessedComparisonTerminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set.Icc (0 : ℝ) DurationAt[later,r] →
      (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  extendHalfOpenInterval (sub_pos.mpr ((R.terminalTime_strictMono r) ordered))
    LiftAt[S,later,ordered,r,side]

local notation "FullBankAt[" S "," L "," h "," r "," side "]" =>
  K.compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S L h r side

open Classical in
/-- Completing the endpoint retains the exact original speed bound on the closed interval. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_lipschitz
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    LipschitzWith (Dilation.ratio OriginalAt[S,r,side]) FullBankAt[S,later,ordered,r,side] :=
  extendHalfOpenInterval_lipschitz _ _
    (K.compatibleMeshProcessedComparisonTerminalLift_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side)

open Classical in
/-- Both endpoints, including the new rim endpoint, keep their original whole-cut copies. -/
theorem compatibleMeshProcessedComparisonWholeMap_terminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Icc (0 : ℝ) DurationAt[later,r]) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered (FullBankAt[S,later,ordered,r,side] u) =
        OriginalAt[S,r,side] (offsetNonnegativeIccParameter StartAt[r] u) := by
  have continuous_bank : Continuous (fun t : Set.Icc (0 : ℝ) DurationAt[later,r] =>
      OriginalAt[S,r,side] (offsetNonnegativeIccParameter StartAt[r] t)) :=
    (Dilation.lipschitzWith OriginalAt[S,r,side]).continuous.comp
      (offsetNonnegativeIccParameter_isometry StartAt[r]).continuous
  exact map_extendHalfOpenInterval (sub_pos.mpr ((R.terminalTime_strictMono r) ordered)) _
    (K.compatibleMeshProcessedComparisonTerminalLift_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side)
    (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered)
    (K.compatibleMeshProcessedComparisonWholeMap_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered).continuous _ continuous_bank
    (K.compatibleMeshProcessedComparisonWholeMap_terminalLift compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side) u

open Classical in
/-- Completing the new rim endpoint preserves every original pairwise bank distance. -/
theorem edist_compatibleMeshProcessedComparisonTerminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (s t : Set.Icc (0 : ℝ) DurationAt[later,r]) :
    edist (FullBankAt[S,later,ordered,r,side] s) (FullBankAt[S,later,ordered,r,side] t) =
      edist (OriginalAt[S,r,side] (offsetNonnegativeIccParameter StartAt[r] s))
        (OriginalAt[S,r,side] (offsetNonnegativeIccParameter StartAt[r] t)) := by
  have first := K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered r side s
  have last := K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered r side t
  apply le_antisymm
  · have bound := K.compatibleMeshProcessedComparisonTerminalClosedBank_lipschitz compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side s t
    exact bound.trans_eq
      ((congrArg (fun d : ℝ≥0∞ => (Dilation.ratio OriginalAt[S,r,side] : ℝ≥0∞) * d)
        ((offsetNonnegativeIccParameter_isometry StartAt[r]).edist_eq s t).symm).trans
        (Dilation.edist_eq OriginalAt[S,r,side] _ _).symm)
  · have bound := K.compatibleMeshProcessedComparisonWholeMap_lipschitz compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      (FullBankAt[S,later,ordered,r,side] s) (FullBankAt[S,later,ordered,r,side] t)
    exact (congrArg₂ edist first last).symm.trans_le (bound.trans_eq (one_mul _))

open Classical in
/-- The full actual outer bank is a dilation, including the new rim endpoint. -/
def compatibleMeshProcessedComparisonTerminalClosedBankDilation
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Set.Icc (0 : ℝ) DurationAt[later,r] →ᵈ
      (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  dilationOfIsometricLift OriginalAt[S,r,side] (offsetNonnegativeIccParameter StartAt[r])
    (offsetNonnegativeIccParameter_isometry StartAt[r]) FullBankAt[S,later,ordered,r,side]
    (K.edist_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side)

open Classical in
/-- Both endpoint copies belong to the same closed embedded original outer bank. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_isClosedEmbedding
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Topology.IsClosedEmbedding FullBankAt[S,later,ordered,r,side] :=
  Dilation.isClosedEmbedding
    (K.compatibleMeshProcessedComparisonTerminalClosedBankDilation compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered r side)

open Classical in
/-- Every closed-bank copy keeps its literal original spatial ray point. -/
theorem fold_compatibleMeshProcessedComparisonTerminalClosedBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Icc (0 : ℝ) DurationAt[later,r]) :
    (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      (FullBankAt[S,later,ordered,r,side] u) =
        SpatialEnvelope.point M.plane
          (R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + u.val)) :=
  (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered _).symm.trans
    ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val)
      (K.compatibleMeshProcessedComparisonWholeMap_terminalClosedBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered r side u)).trans
      (K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
        r side (offsetNonnegativeIccParameter StartAt[r] u)))

open Classical in
/-- Before the new rim, completion keeps the individually named canonical finite bank copy. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_eq_bank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Icc (0 : ℝ) DurationAt[later,r]) (before : u.val < DurationAt[later,r]) :
    FullBankAt[S,later,ordered,r,side] u =
      K.compatibleMeshProcessedComparisonTerminalBank compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered r side
        (offsetNonnegativeIccParameter StartAt[r] u)
        (by change R.terminalTime level r + u.val < R.terminalTime later r; linarith) :=
  extendHalfOpenInterval_before _ _
    (K.compatibleMeshProcessedComparisonTerminalLift_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side) u before

open Classical in
/-- The entire completed outer bank lies on the actual cut boundary, including its new rim. -/
theorem compatibleMeshProcessedComparisonTerminalClosedBank_mem_boundary
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (u : Set.Icc (0 : ℝ) DurationAt[later,r]) :
    FullBankAt[S,later,ordered,r,side] u ∈
      (NewAt[S,later,ordered]).pairedComplex.bankBoundary NewRetainAt[S,later,ordered] := by
  let x := FullBankAt[S,later,ordered,r,side] u
  have position : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered] x) =
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + u.val) :=
    (congrArg Cap.horizontal
      (K.fold_compatibleMeshProcessedComparisonTerminalClosedBank compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered r side u)).trans
      (SpatialEnvelope.horizontal_point _ _)
  by_cases before : u.val < DurationAt[later,r]
  · exact K.compatibleMeshProcessedComparison_mem_boundary_of_terminal_position compact nonempty R
      no_boundary level higher M positive inner_disk beta acute S later ordered r
      (offsetNonnegativeIccParameter StartAt[r] u)
      (by change _ ≤ _ + u.val; linarith [u.property.1])
      (by change _ + u.val < _; linarith) x position
  · have endpoint : R.terminalTime level r + u.val = R.terminalTime later r := by
      linarith [u.property.2, not_lt.mp before]
    let included := Set.subset_univ NewRetainAt[S,later,ordered]
    have projected : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace Set.univ
        ((NewAt[S,later,ordered]).pairedComplex.forgetCuts included x)) =
          R.terminalPoint later r :=
      (congrArg Cap.horizontal
        ((NewAt[S,later,ordered]).pairedFolding.toSpace_forgetCuts included x)).trans
        (position.trans (congrArg (R.exterior.ray (R.terminalIndex r)) endpoint))
    let roof := (NewAt[S,later,ordered]).toTriangulation.roof ConformingAt[S,later,ordered]
      (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M)
    have on_rim : R.terminalPoint later r ∈ frontier roof.footprint := by
      rw [(NewAt[S,later,ordered]).toTriangulation.roof_footprint, M.clip_eq_sublevel, neg_neg]
      exact R.terminalPoint_mem_frontier later HigherAt[later,ordered] r
    apply (NewAt[S,later,ordered]).pairedComplex.bankBoundary_preimage_forgetCuts included
    apply (roof.projected_mem_frontier_iff_bankBoundary _).mp
    exact Eq.mpr (congrArg (fun p : Plane => p ∈ frontier roof.footprint) projected) on_rim

end Unfoldings.ConvexRoof
