module

public import Unfoldings.Roof.CompatibleComparisonTerminalCompletion
public import Unfoldings.Roof.TerminalBandParameters
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.SpatialEnvelopeDirectedBanks
public import Unfoldings.Complex.DirectedBoundaryPathReversal

/-! Recover whole directed fine edges from nonvertex contacts with original terminal bands. -/

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

local instance comparisonTerminalAlignmentIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalAlignmentNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalAlignmentWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- A respected prescribed segment containing a nonvertex edge contact contains the
whole fine edge, including both endpoints. The old terminal band is a prescribed segment. -/
theorem compatibleMeshProcessedComparison_terminal_segment_aligned
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (f : (NewAt[S,later,ordered]).Index) (e : Fin 3)
    (x : ((NewAt[S,later,ordered]).projectedTriangle f).Edge e)
    (regular : ¬ ((NewAt[S,later,ordered]).projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ segment ℝ (R.terminalPoint level r) (R.terminalPoint later r)) :
    ((NewAt[S,later,ordered]).projectedTriangle f).edge e ⊆
      segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
  have pair_member : (R.terminalPoint level r, R.terminalPoint later r) ∈ PairsAt[S,later] :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  let pair : {p // p ∈ PairsAt[S,later]} :=
    ⟨(R.terminalPoint level r, R.terminalPoint later r), pair_member⟩
  let U := triangleWithEdge pair.val.1 pair.val.2
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S ordered pair)
  exact U.edge_subset_of_signed_coords ((NewAt[S,later,ordered]).projectedTriangle f)
    (fun k => (NewAt[S,later,ordered]).signs f (pair, k))
    (fun k p hp => (NewAt[S,later,ordered]).constrained f p hp (pair, k)) 0 e x regular member

open Classical in
/-- One nonvertex contact orients an entire original comparison fine bank along its
terminal band. Both original endpoint parameters and the intrinsic contact copy survive. -/
theorem exists_compatibleMeshProcessedComparison_forward_terminal_bank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots})
    (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
    (u : unitInterval)
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v)
    (member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u)) ∈
        segment ℝ (R.terminalPoint level r) (R.terminalPoint later r)) :
    ∃ (q : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (s t : Set.Icc (0 : ℝ) DurationAt[later,r]), s.val < t.val ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition q) =
        R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + s.val) ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] q)) =
          R.exterior.ray (R.terminalIndex r) (R.terminalTime level r + t.val) ∧
      ∃ v : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath q v =
        (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u := by
  let bank := ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
    NewRetainAt[S,later,ordered] p).1
  have aligned := K.compatibleMeshProcessedComparison_terminal_segment_aligned compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered r bank.val.face
    bank.val.edge
    ⟨_, (NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p u⟩
    ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_nonvertex p u regular)
    member
  have entire (v : unitInterval) := aligned
    ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p v)
  have first_member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p) ∈
      segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
    have initial := entire 0
    rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at initial
    change AffineMap.lineMap _ _ (0 : ℝ) ∈ _ at initial
    simpa only [AffineMap.lineMap_apply_zero] using initial
  have last_member : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p)) ∈
      segment ℝ (R.terminalPoint level r) (R.terminalPoint later r) := by
    have final := entire 1
    rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at final
    change AffineMap.lineMap _ _ (1 : ℝ) ∈ _ at final
    simpa only [AffineMap.lineMap_apply_one] using final
  obtain ⟨s, first⟩ := R.exists_terminal_band_parameter_of_mem_segment ordered r first_member
  obtain ⟨t, last⟩ := R.exists_terminal_band_parameter_of_mem_segment ordered r last_member
  have different : s.val ≠ t.val := by
    intro same
    exact (NewAt[S,later,ordered]).toTriangulation.horizontal_boundaryPosition_ne p
      (first.trans ((congrArg (fun z => R.exterior.ray (R.terminalIndex r)
        (R.terminalTime level r + z)) same).trans last.symm))
  rcases lt_or_gt_of_ne different with forward | backward
  · exact ⟨p, s, t, forward, first, last, u, rfl⟩
  · refine ⟨(NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p,
      t, s, backward, last, ?_, ?_⟩
    · rwa [(NewAt[S,later,ordered]).pairedComplex.boundaryTurn_involutive]
    · refine ⟨⟨1 - u.val, sub_nonneg.mpr u.property.2, sub_le_self _ u.property.1⟩, ?_⟩
      rw [(NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_turn]
      apply congrArg ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p)
      apply Subtype.ext
      change 1 - (1 - u.val) = u.val
      ring

end Unfoldings.ConvexRoof
