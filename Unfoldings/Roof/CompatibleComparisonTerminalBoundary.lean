module

public import Unfoldings.Roof.CompatibleComparisonTerminalIntervals
public import Unfoldings.Roof.SpatialEnvelopeCutBoundaryFibers
public import Unfoldings.Roof.SpatialEnvelopeInteriorSeams
public import Unfoldings.Complex.BoundaryPointPath

/-! Actual intrinsic boundary copies of whole original terminal intervals in comparison meshes. -/

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

local instance comparisonTerminalBoundaryIndexFintype : Fintype (T).Index :=
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
local instance comparisonTerminalBoundaryNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonTerminalBoundaryWholeFintype : Fintype W.Index := W.finiteIndex

local notation "BankAt[" S "," r "," side "," t "]" =>
  K.restoredWholeTerminalBank compact nonempty R no_boundary W CutsAt[S] IncludedAt[S] r side t
local notation "TerminalAt[" S "," L "," h "," r "," side "," t "," ht "]" =>
  K.compatibleMeshProcessedComparisonTerminalBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h r side t ht
local notation "IntervalAt[" S "," L "," h "," r "," side "," a "," b "," hb "]" =>
  K.compatibleMeshProcessedComparisonTerminalInterval compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h r side a b hb

open Classical in
/-- Every canonical finite cut segment stays inside the larger closed comparison window. -/
theorem compatibleMeshProcessedWindowPair_segment_subset_clip
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level ≤ later)
    (pair : {p // p ∈ PairsAt[S,later]}) :
    segment ℝ pair.val.1 pair.val.2 ⊆ SpatialEnvelope.clip M.plane (-later) := by
  intro p on_segment
  have member : p ∈ K.compatibleMeshProcessedWindowCarrier compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later := by
    rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs]
    exact Set.mem_iUnion.mpr ⟨pair, on_segment⟩
  rw [← K.compatibleMeshProcessedCarrier_inter_sublevel compact nonempty R no_boundary level higher
    M positive inner_disk beta acute S ordered] at member
  rw [M.clip_eq_sublevel, neg_neg]
  exact member.2

open Classical in
/-- Every original outer terminal point in the new window lies on a genuine removed new seam.
This includes the old truncation endpoint and every fine subdivision vertex. -/
theorem exists_compatibleMeshProcessedComparison_terminal_cut_seam
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (t : ℝ≥0)
    (after : R.terminalTime level r ≤ t.val) (before : t.val < R.terminalTime later r) :
    ∃ s : (NewAt[S,later,ordered]).pairedComplex.Seam,
      s ∉ NewRetainAt[S,later,ordered] ∧
      R.exterior.ray (R.terminalIndex r) t.val ∈
        ((NewAt[S,later,ordered]).projectedTriangle
          ((NewAt[S,later,ordered]).pairedComplex.left s).face).edge
          ((NewAt[S,later,ordered]).pairedComplex.left s).edge := by
  let p := R.exterior.ray (R.terminalIndex r) t.val
  have below := (R.terminal_ray_below_iff later (fun v => (higher v).trans ordered) r
    t.property).mpr before
  have in_clip : p ∈ SpatialEnvelope.clip M.plane (-later) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact below.le
  have in_cut : p ∈ CutsAt[S] := Or.inl
    ⟨Or.inr (Set.mem_iUnion.mpr ⟨r, t.val, t.property, rfl⟩),
      (R.terminal_ray_superlevel_iff level higher r t.property).mpr after⟩
  have finite_member := (K.compatibleMeshProcessedWindowCarrier_agree compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S ordered.le in_clip).mp in_cut
  rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs] at finite_member
  obtain ⟨pair, on_segment⟩ := Set.mem_iUnion.mp finite_member
  have segment_inside := K.compatibleMeshProcessedWindowPair_segment_subset_clip compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered.le pair
  have cover := (NewAt[S,later,ordered]).prescribed_segment_eq_union_subedges
    (fun q : {q // q ∈ PairsAt[S,later]} => q.val.1) (fun q => q.val.2)
    (K.compatibleMeshProcessedWindowPairs_ne compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S ordered) pair
    (segment_inside (left_mem_segment ℝ _ _)) (segment_inside (right_mem_segment ℝ _ _))
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (cover.subset on_segment)
  have selected : ((NewAt[S,later,ordered]).projectedTriangle e.val.1).edge e.val.2 ⊆
      CutsAt[S] := by
    intro z member
    have z_inside := (NewAt[S,later,ordered]).cover.symm.subset (Set.mem_iUnion.mpr
      ⟨e.val.1, ((NewAt[S,later,ordered]).projectedTriangle e.val.1).edge_subset _ member⟩)
    apply (K.compatibleMeshProcessedWindowCarrier_agree compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S ordered.le z_inside).mpr
    rw [K.compatibleMeshProcessedWindowCarrier_eq_pairs]
    exact Set.mem_iUnion.mpr ⟨pair, e.property member⟩
  have interior_point : p ∈ interior (SpatialEnvelope.clip M.plane (-later)) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
  obtain ⟨s, removed, incident⟩ :=
    (NewAt[S,later,ordered]).toTriangulation.exists_cut_seam_of_projected_edge
      ConformingAt[S,later,ordered]
      (K.compatible_section_interior compact nonempty R later (fun v => (higher v).trans ordered) M)
      CutsAt[S] ⟨e.val.1, e.val.2⟩ selected on_edge interior_point
  refine ⟨s, removed, ?_⟩
  rcases incident with first | last
  · exact (congrArg (fun a : EdgeRef (NewAt[S,later,ordered]).Index =>
      ((NewAt[S,later,ordered]).projectedTriangle a.face).edge a.edge) first).subset on_edge
  · rw [(NewAt[S,later,ordered]).paired_seam_projected_edge]
    exact (congrArg (fun a : EdgeRef (NewAt[S,later,ordered]).Index =>
      ((NewAt[S,later,ordered]).projectedTriangle a.face).edge a.edge) last).subset on_edge

open Classical in
/-- Every actual intrinsic copy above an original outer terminal point lies on the original
comparison cut boundary, even at vertices and when the copy has a different face tag. -/
theorem compatibleMeshProcessedComparison_mem_boundary_of_terminal_position
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (t : ℝ≥0)
    (after : R.terminalTime level r ≤ t.val) (before : t.val < R.terminalTime later r)
    (x : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (position : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered] x) = R.exterior.ray (R.terminalIndex r) t.val) :
    x ∈ (NewAt[S,later,ordered]).pairedComplex.bankBoundary NewRetainAt[S,later,ordered] := by
  obtain ⟨s, removed, on_edge⟩ :=
    K.exists_compatibleMeshProcessedComparison_terminal_cut_seam compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S later ordered r t
    after before
  let q := ((NewAt[S,later,ordered]).edgeProjection
    ((NewAt[S,later,ordered]).pairedComplex.left s).face
    ((NewAt[S,later,ordered]).pairedComplex.left s).edge).symm
    ⟨R.exterior.ray (R.terminalIndex r) t.val, on_edge⟩
  have projected : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.place
      ((NewAt[S,later,ordered]).pairedComplex.left s).face q.val) =
      R.exterior.ray (R.terminalIndex r) t.val :=
    ((M.plane ((NewAt[S,later,ordered]).support
      ((NewAt[S,later,ordered]).pairedComplex.left s).face)).horizontal_place q.val).trans
      ((M.plane ((NewAt[S,later,ordered]).support
        ((NewAt[S,later,ordered]).pairedComplex.left s).face)).project.apply_symm_apply _)
  exact (NewAt[S,later,ordered]).toTriangulation.mem_bankBoundary_of_projected_cut_edge
    ConformingAt[S,later,ordered] NewRetainAt[S,later,ordered] s removed q x
    (position.trans projected.symm)

open Classical in
/-- Every point of the whole original closed terminal interval is an actual finite cut-boundary
copy, with both original endpoints retained. The final endpoint is inside the new window. -/
theorem compatibleMeshProcessedComparisonTerminalInterval_mem_boundary
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (after : R.terminalTime level r ≤ first.val) (before : last.val < R.terminalTime later r)
    (u : Set.Icc (first : ℝ) (last : ℝ)) :
    IntervalAt[S,later,ordered,r,side,first,last,before] u ∈
      (NewAt[S,later,ordered]).pairedComplex.bankBoundary NewRetainAt[S,later,ordered] := by
  apply K.compatibleMeshProcessedComparison_mem_boundary_of_terminal_position compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered r
    (nonnegativeIntervalCopy first last u) (after.trans u.property.1)
    (u.property.2.trans_lt before)
  exact (congrArg Cap.horizontal
    (K.fold_compatibleMeshProcessedComparisonTerminalInterval compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered r side first last before u)).trans
        (SpatialEnvelope.horizontal_point _ _)

open Classical in
/-- Every original closed terminal-interval copy lies on an actual directed fine bank.
The construction needs neither a supplied global boundary contour nor a fan certificate. -/
theorem exists_directedBank_at_compatibleMeshProcessedComparisonTerminalInterval
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (r : {v // v ∈ R.parents.roots}) (side : Bool) (first last : ℝ≥0)
    (after : R.terminalTime level r ≤ first.val) (before : last.val < R.terminalTime later r)
    (u : Set.Icc (first : ℝ) (last : ℝ)) :
    ∃ (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (t : unitInterval),
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p t =
        IntervalAt[S,later,ordered,r,side,first,last,before] u :=
  (NewAt[S,later,ordered]).pairedComplex.exists_directedBoundaryPath_of_mem_boundary
    (K.compatibleMeshProcessedComparisonTerminalInterval_mem_boundary compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered r side first last
      after before u)

end Unfoldings.ConvexRoof
