module

public import Unfoldings.Roof.CompatibleComparisonFiniteMatching
public import Unfoldings.Geometry.SpatialEnvelopeCutBankSegments
public import Unfoldings.Geometry.SpatialEnvelopeBankOrientation
public import Unfoldings.Roof.SpatialEnvelopeFoldingGraph
public import Unfoldings.Topology.ClosedIntervalFiniteExceptions

/-! Construct entire matching forward fine-bank pieces from original finite-bank contacts. -/

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

local instance comparisonFinitePiecesIndexFintype : Fintype (T).Index :=
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
local instance comparisonFinitePiecesNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFinitePiecesWholeFintype : Fintype W.Index := W.finiteIndex

local notation "OldEndAt[" S "," s "," side "," flag "]" =>
  Equiv.symm (TriangleComplex.boundaryEndEquiv
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) RetainAt[S])
    (TriangleComplex.cutBank (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) RetainAt[S] s side, flag)
local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

open Classical in
/-- A nonvertex contact on an original lifted finite bank constructs a whole forward
fine bank with its exact original parameter interval and all intrinsic copies.
Neither original endpoint positions nor side matching are assumed. -/
theorem exists_compatibleMeshProcessedComparisonFiniteCutBank_piece
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool) (u : unitInterval)
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] u ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v) :
    ∃ (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (first last : unitInterval) (forward : first.val < last.val),
      (∀ v : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p v =
        LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
          (closedUnitIntervalLineMap first last forward.le v)) ∧
      ∃ v : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p v =
        LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] u := by
  obtain ⟨p, t, at_point⟩ :=
    K.exists_directedBank_at_compatibleMeshProcessedComparisonFiniteCutBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered s.val s.property
      side flag u
  let bank := ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
    NewRetainAt[S,later,ordered] p).1
  let pair : {p // p ∈ PairsAt[S,later]} :=
    ⟨(((T).projectedTriangle ((T).pairedComplex.left s.val).face).vertex
        ((T).pairedComplex.left s.val).edge,
      ((T).projectedTriangle ((T).pairedComplex.left s.val).face).vertex
        (Triangle.next ((T).pairedComplex.left s.val).edge)), by
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩
      rw [(T).toTriangulation.roof_projectedTriangle conforming inside]⟩
  have on_segment := K.compatibleMeshProcessedComparisonFiniteCutBank_mem_segment compact nonempty
    R no_boundary level higher M positive inner_disk beta acute W S later ordered s.val s.property
      side flag u
  have contact_member := (congrArg (fun z => Cap.horizontal
    ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered] z) ∈
      segment ℝ pair.val.1 pair.val.2) at_point).mpr on_segment
  have aligned := K.compatibleMeshProcessedComparison_pair_segment_aligned compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered pair bank.val.face
    bank.val.edge
    ⟨_, (NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p t⟩
    ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_nonvertex p t
      (fun vertex same => regular vertex (at_point.symm.trans same))) contact_member
  have source_segment := (T).toTriangulation.horizontal_cutBank_directed_segment RetainAt[S]
    s side flag
  have entire (v : unitInterval) :
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p v)) ∈
      segment ℝ ((Cap.horizontal ((T).pairedFolding.boundaryPosition OldEndAt[S,s,side,flag])))
        (Cap.horizontal ((T).pairedFolding.boundaryPosition
          ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))) :=
    source_segment.symm ▸ aligned
      ((NewAt[S,later,ordered]).toTriangulation.horizontal_directedBoundaryPath_mem_edge p v)
  have initial_member := entire 0
  have final_member := entire 1
  rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at initial_member
  rw [(NewAt[S,later,ordered]).pairedFolding.horizontal_directedBoundaryPath] at final_member
  change AffineMap.lineMap _ _ (0 : ℝ) ∈ _ at initial_member
  change AffineMap.lineMap _ _ (1 : ℝ) ∈ _ at final_member
  rw [AffineMap.lineMap_apply_zero] at initial_member
  rw [AffineMap.lineMap_apply_one] at final_member
  obtain ⟨q, first, last, forward, initial, final, v, at_p⟩ :=
    (NewAt[S,later,ordered]).toTriangulation.exists_forward_bank_of_segment_endpoints p _ _
      initial_member final_member t
  have at_original := at_p.trans at_point
  have same_spatial (x : (NewAt[S,later,ordered]).pairedComplex.Realization
      NewRetainAt[S,later,ordered]) (y : (T).pairedComplex.Realization RetainAt[S])
      (same_horizontal : Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] x) =
          Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S] y)) :
      (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered] x =
        (T).pairedFolding.toSpace RetainAt[S] y :=
    ((NewAt[S,later,ordered]).toTriangulation.toSpace_eq_point NewRetainAt[S,later,ordered] x).trans
      ((congrArg (SpatialEnvelope.point M.plane) same_horizontal).trans
        ((T).toTriangulation.toSpace_eq_point RetainAt[S] y).symm)
  have initial_space := same_spatial _ _
    (initial.trans ((T).pairedFolding.horizontal_directedBoundaryPath
      OldEndAt[S,s,side,flag] first).symm)
  have final_space := same_spatial _ _
    (final.trans ((T).pairedFolding.horizontal_directedBoundaryPath
      OldEndAt[S,s,side,flag] last).symm)
  have interior_time := (NewAt[S,later,ordered]).toTriangulation.directedBoundaryPath_time_interior
    q v (fun vertex same => regular vertex (at_original.symm.trans same))
  let clock := closedUnitIntervalLineMap first last forward.le
  have physical := ((NewAt[S,later,ordered]).pairedFolding.directedBoundaryPath_lineMap q v).trans
    ((congrArg₂ (fun x y : Space => AffineMap.lineMap x y v.val) initial_space final_space).trans
      ((T).pairedFolding.directedBoundaryPath_subinterval OldEndAt[S,s,side,flag]
        first last forward.le v).symm)
  have at_source := (congrArg (fun z => (NewAt[S,later,ordered]).pairedFolding.toSpace
    NewRetainAt[S,later,ordered] z) at_original).trans
      (K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] u)
  have same_clock := (T).toTriangulation.horizontal_directedBoundaryPath_injective
    OldEndAt[S,s,side,flag] ((congrArg Cap.horizontal physical).symm.trans
      (congrArg Cap.horizontal at_source))
  have contact := at_original.trans
    (congrArg LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] same_clock.symm)
  exact ⟨q, first, last, forward,
    K.compatibleMeshProcessedComparison_directedBank_finiteCutBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered s side flag q first last
      forward initial_space final_space v interior_time contact, v, at_original⟩

open Classical in
/-- Actual forward fine banks that retain an entire original finite-bank subinterval. -/
def compatibleMeshProcessedComparisonFiniteBankEnds
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool) :
    Set ((NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered]) :=
  {p | ∃ (first last : unitInterval) (forward : first.val < last.val),
    ∀ u : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
      LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
        (closedUnitIntervalLineMap first last forward.le u)}

open Classical in
/-- Whole forward fine banks cover every point of the original finite bank,
including subdivision vertices and both original endpoint copies. -/
theorem compatibleMeshProcessedComparisonFiniteBank_range_eq_union_directedBanks
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool) :
    Set.range LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] =
      ⋃ p : K.compatibleMeshProcessedComparisonFiniteBankEnds compact nonempty R no_boundary level
          higher M positive inner_disk beta acute W S later ordered s side flag,
        Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p.val) := by
  let curve := LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
  let ends := K.compatibleMeshProcessedComparisonFiniteBankEnds compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered s side flag
  let pieces := ⋃ p : ends,
    Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p.val)
  have closed : IsClosed pieces := isClosed_iUnion_of_finite
    (fun p : ends => (isCompact_range
      ((NewAt[S,later,ordered]).pairedComplex.continuous_directedBoundaryPath p.val)).isClosed)
  have embedded := K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty
    R no_boundary level higher M positive inner_disk beta acute W S later ordered
    OldEndAt[S,s,side,flag]
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
    obtain ⟨p, first, last, forward, entire, u, contact⟩ :=
      K.exists_compatibleMeshProcessedComparisonFiniteCutBank_piece compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered s side flag t nonvertex
    exact missing (Set.mem_iUnion.mpr ⟨⟨p, first, last, forward, entire⟩, u, contact⟩))
  have covered := continuous_Icc_mem_closed_of_finite_exceptions zero_lt_one curve
    (Dilation.lipschitzWith curve).continuous closed exceptions
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact covered t
  · intro x member
    obtain ⟨p, u, rfl⟩ := Set.mem_iUnion.mp member
    obtain ⟨first, last, forward, entire⟩ := p.property
    exact ⟨_, (entire u).symm⟩

end Unfoldings.ConvexRoof
