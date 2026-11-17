module

public import Unfoldings.Roof.CompatibleComparisonTerminalCharts
public import Unfoldings.Metric.NonnegativeIntervalCopy

/-! Exact closed terminal intervals in actual larger intermediate-cut comparison meshes. -/

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

local instance comparisonTerminalIntervalIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalIntervalNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalIntervalWholeFintype : Fintype W.Index := W.finiteIndex

local notation "BankAt[" S "," r "," side "," t "]" =>
  K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side t

/-- An entire original closed terminal interval, parametrized by its literal real times. -/
def compatibleMeshProcessedTerminalIntervalDilation (S : (Fcut).parents.ParentFrontier)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0) :
    Set.Icc (first : ℝ) (last : ℝ) →ᵈ W.partition.Cut CutsAt[S] :=
  (K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W CutsAt[S] IncludedAt[S]
    r side).comp (Isometry.toDilation _ (isometry_nonnegativeIntervalCopy first last))

local notation "OriginalIntervalAt[" S "," r "," side "," a "," b "]" =>
  K.compatibleMeshProcessedTerminalIntervalDilation compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S r side a b

/-- Every point of the entire closed terminal interval lies strictly inside the chosen
larger window; the final original time alone supplies the necessary height bound. -/
theorem compatibleMeshProcessedTerminalInterval_positive (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (first last : ℝ≥0) (before : last.val < R.terminalTime later r)
    (u : Set.Icc (first : ℝ) (last : ℝ)) :
    ∀ j, 0 < SpatialEnvelope.levelEquation M.plane (-later) j
      (Cap.horizontal (W.partition.restoreCut CutsAt[S]
        (OriginalIntervalAt[S,r,side,first,last] u)).val) := by
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  have below := K.compatibleMeshProcessed_terminal_below_comparison compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered r side
    (nonnegativeIntervalCopy first last u) (u.property.2.trans_lt before)
  change -later < -(K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut CutsAt[S]
      BankAt[S,r,side,nonnegativeIntervalCopy first last u]).val)
  linarith

open Classical in
/-- Lift the whole closed original terminal interval as a metric dilation into the actual
larger comparison mesh. Original endpoints and every pairwise distance are retained. -/
def compatibleMeshProcessedComparisonTerminalInterval
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) :
    Set.Icc (first : ℝ) (last : ℝ) →ᵈ
      (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  (VAt[later,ordered]).partialPairedMeshCurveLiftDilation ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (first : ℝ) (last : ℝ)) (convex_Icc _ _)
    OriginalIntervalAt[S,r,side,first,last]
    (K.compatibleMeshProcessedTerminalInterval_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side first last before)

local notation "IntervalAt[" S "," L "," h "," r "," side "," a "," b "," hb "]" =>
  K.compatibleMeshProcessedComparisonTerminalInterval compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h r side a b hb

open Classical in
/-- The complete interval and the individually named terminal-bank copies agree literally. -/
theorem compatibleMeshProcessedComparisonTerminalInterval_eq_bank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) (u : Set.Icc (first : ℝ) (last : ℝ)) :
    IntervalAt[S,later,ordered,r,side,first,last,before] u =
      K.compatibleMeshProcessedComparisonTerminalBank compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered r side
        (nonnegativeIntervalCopy first last u)
        (u.property.2.trans_lt before) := rfl

open Classical in
/-- The finite interval retains each literal original cut copy, with its original time. -/
theorem compatibleMeshProcessedComparisonWholeMap_terminalInterval
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) (u : Set.Icc (first : ℝ) (last : ℝ)) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered
      (IntervalAt[S,later,ordered,r,side,first,last,before] u) =
        BankAt[S,r,side,nonnegativeIntervalCopy first last u] :=
  (VAt[later,ordered]).partialPairedMeshMap_curveLift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (first : ℝ) (last : ℝ)) OriginalIntervalAt[S,r,side,first,last]
    (K.compatibleMeshProcessedTerminalInterval_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side first last before) u

open Classical in
/-- The original full spatial ray point is retained at every closed interval parameter. -/
theorem fold_compatibleMeshProcessedComparisonTerminalInterval
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) (u : Set.Icc (first : ℝ) (last : ℝ)) :
    (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      (IntervalAt[S,later,ordered,r,side,first,last,before] u) =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) u.val) := by
  exact (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S later ordered _).symm.trans
      ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val)
        (K.compatibleMeshProcessedComparisonWholeMap_terminalInterval compact nonempty R no_boundary
          level higher M positive inner_disk beta acute W S later ordered r side first last before
            u)).trans
        (K.restore_restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S]
          IncludedAt[S] r side (nonnegativeIntervalCopy first last u)))

open Classical in
/-- Every two fine interval points have exactly their original terminal-bank distance. -/
theorem edist_compatibleMeshProcessedComparisonTerminalInterval
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) (u v : Set.Icc (first : ℝ) (last : ℝ)) :
    edist (IntervalAt[S,later,ordered,r,side,first,last,before] u)
        (IntervalAt[S,later,ordered,r,side,first,last,before] v) =
      edist BankAt[S,r,side,nonnegativeIntervalCopy first last u]
        BankAt[S,r,side,nonnegativeIntervalCopy first last v] :=
  (VAt[later,ordered]).edist_partialPairedMeshCurveLift_dilation ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (first : ℝ) (last : ℝ)) (convex_Icc _ _) OriginalIntervalAt[S,r,side,first,last]
    (K.compatibleMeshProcessedTerminalInterval_positive compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side first last before) u v

open Classical in
/-- The full closed interval is embedded and closed, including both original endpoints. -/
theorem compatibleMeshProcessedComparisonTerminalInterval_isClosedEmbedding
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (before : last.val < R.terminalTime later r) :
    Topology.IsClosedEmbedding IntervalAt[S,later,ordered,r,side,first,last,before] :=
  Dilation.isClosedEmbedding IntervalAt[S,later,ordered,r,side,first,last,before]

end Unfoldings.ConvexRoof
