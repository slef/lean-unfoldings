module

public import Unfoldings.Roof.CompatibleComparisonTerminalBoundary
public import Unfoldings.Roof.CompatibleComparisonFiniteBanks
public import Unfoldings.Complex.ClosedBanks
public import Unfoldings.Complex.DirectedBoundaryPathBank

/-! Actual interior copies of the original cuts belong to the finite comparison cut boundary. -/

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

local instance comparisonCutBoundaryIndexFintype : Fintype (T).Index :=
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
local instance comparisonCutBoundaryNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonCutBoundaryWholeFintype : Fintype W.Index := W.finiteIndex

open Classical in
/-- Every point of the original cut strictly inside the larger window lies on a
genuine removed comparison seam, including original endpoints and subdivision vertices. -/
theorem exists_compatibleMeshProcessedComparison_cut_seam
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : Plane) (in_cut : p ∈ CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height p < later) :
    ∃ s : (NewAt[S,later,ordered]).pairedComplex.Seam,
      s ∉ NewRetainAt[S,later,ordered] ∧
      p ∈ ((NewAt[S,later,ordered]).projectedTriangle
        ((NewAt[S,later,ordered]).pairedComplex.left s).face).edge
        ((NewAt[S,later,ordered]).pairedComplex.left s).edge := by
  have in_clip : p ∈ SpatialEnvelope.clip M.plane (-later) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact below.le
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
      (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M)
      CutsAt[S] ⟨e.val.1, e.val.2⟩ selected on_edge interior_point
  refine ⟨s, removed, ?_⟩
  rcases incident with first | last
  · exact (congrArg (fun a : EdgeRef (NewAt[S,later,ordered]).Index =>
      ((NewAt[S,later,ordered]).projectedTriangle a.face).edge a.edge) first).subset on_edge
  · rw [(NewAt[S,later,ordered]).paired_seam_projected_edge]
    exact (congrArg (fun a : EdgeRef (NewAt[S,later,ordered]).Index =>
      ((NewAt[S,later,ordered]).projectedTriangle a.face).edge a.edge) last).subset on_edge


open Classical in
/-- Every intrinsic comparison copy over an interior point of the original cut is an
actual cut-boundary point, including all copies at subdivision vertices. -/
theorem compatibleMeshProcessedComparison_mem_boundary_of_cut_position
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : Plane) (in_cut : p ∈ CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height p < later)
    (x : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (position : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
      NewRetainAt[S,later,ordered] x) = p) :
    x ∈ (NewAt[S,later,ordered]).pairedComplex.bankBoundary NewRetainAt[S,later,ordered] := by
  obtain ⟨s, removed, on_edge⟩ :=
    K.exists_compatibleMeshProcessedComparison_cut_seam compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered p in_cut below
  let q := ((NewAt[S,later,ordered]).edgeProjection
    ((NewAt[S,later,ordered]).pairedComplex.left s).face
    ((NewAt[S,later,ordered]).pairedComplex.left s).edge).symm
    ⟨p, on_edge⟩
  have projected : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.place
      ((NewAt[S,later,ordered]).pairedComplex.left s).face q.val) =
      p :=
    ((M.plane ((NewAt[S,later,ordered]).support
      ((NewAt[S,later,ordered]).pairedComplex.left s).face)).horizontal_place q.val).trans
      ((M.plane ((NewAt[S,later,ordered]).support
        ((NewAt[S,later,ordered]).pairedComplex.left s).face)).project.apply_symm_apply _)
  exact (NewAt[S,later,ordered]).toTriangulation.mem_bankBoundary_of_projected_cut_edge
    ConformingAt[S,later,ordered] NewRetainAt[S,later,ordered] s removed q x
    (position.trans projected.symm)

/-- Both labeled banks of every removed original seam project into the original cut. -/
theorem compatibleMeshProcessed_cutBank_mem_cut
    (S : (Fcut).parents.ParentFrontier) (s : (T).pairedComplex.Seam)
    (removed : s ∉ RetainAt[S]) (side : Bool)
    (q : ((T).pairedComplex.triangle
      ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side).val.face).Edge
      ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side).val.edge) :
    Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
      ((T).pairedComplex.bankMap RetainAt[S]
        ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side) q)) ∈ CutsAt[S] := by
  have folded := (T).pairedFolding.toSpace_bankMap
    ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side) q
  apply (congrArg (fun z : Space => Cap.horizontal z ∈ CutsAt[S]) folded).mpr
  cases side
  · exact K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S s removed q
  · have joined := (T).pairedFolding.joined s ((T).pairedComplex.identify s |>.symm q)
    have physical := (congrArg (fun z => (T).pairedFolding.place
      ((T).pairedComplex.right s).face z.val)
      ((T).pairedComplex.identify s |>.apply_symm_apply q))
    have equal := joined.trans physical
    exact (congrArg Cap.horizontal equal) ▸
      (K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level higher M
        positive inner_disk beta acute S s removed ((T).pairedComplex.identify s |>.symm q))

open Classical in
/-- The entire lift of either original removed bank lies on the actual larger cut
boundary. The original bank label, orientation and both endpoint copies are retained. -/
theorem compatibleMeshProcessedComparisonFiniteCutBank_mem_boundary
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (side flag : Bool) (u : unitInterval) :
    K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered
      (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
        ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side, flag)) u ∈
      (NewAt[S,later,ordered]).pairedComplex.bankBoundary NewRetainAt[S,later,ordered] := by
  let bank := (T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side
  let p := ((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm (bank, flag)
  have parameter := (T).pairedComplex.directedBoundaryPath_from_bank bank flag u
  have folded := K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered p u
  have on_cut := K.compatibleMeshProcessed_cutBank_mem_cut compact nonempty R no_boundary level
    higher M positive inner_disk beta acute S s removed side
      ((T).pairedComplex.bankParameterFromEnd bank flag u)
  have cut : Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
      ((T).pairedComplex.directedBoundaryPath p u)) ∈ CutsAt[S] :=
    (congrArg (fun z => Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] z) ∈ CutsAt[S])
      parameter).mpr on_cut
  have in_clip := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S]
    ((T).pairedComplex.directedBoundaryPath p u)
  rw [M.clip_eq_sublevel, neg_neg] at in_clip
  exact K.compatibleMeshProcessedComparison_mem_boundary_of_cut_position compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered _ cut
    (in_clip.trans_lt ordered) _ (congrArg Cap.horizontal folded)

open Classical in
/-- Every lifted original removed-bank point has a genuine directed fine-bank
representation, including its original endpoints and all fine subdivision vertices. -/
theorem exists_directedBank_at_compatibleMeshProcessedComparisonFiniteCutBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (side flag : Bool) (u : unitInterval) :
    ∃ (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (t : unitInterval),
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p t =
        K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W S later ordered
          (((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm
            ((T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side, flag)) u :=
  (NewAt[S,later,ordered]).pairedComplex.exists_directedBoundaryPath_of_mem_boundary
    (K.compatibleMeshProcessedComparisonFiniteCutBank_mem_boundary compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered s removed side flag u)

end Unfoldings.ConvexRoof
