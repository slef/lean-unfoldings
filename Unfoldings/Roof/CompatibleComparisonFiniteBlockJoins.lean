module

public import Unfoldings.Roof.CompatibleComparisonFiniteChainModel
public import Unfoldings.Roof.CompatibleProcessedCutBankInterior
public import Unfoldings.Roof.CompatibleProcessedComparisonFiber
public import Unfoldings.Complex.BoundaryChainConcatenation

/-! Original bank labels and endpoint copies determine separation and actual fine-block joins. -/

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

local instance comparisonFiniteBlockJoinsIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteBlockJoinsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteBlockJoinsWholeFintype : Fintype W.Index := W.finiteIndex

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

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {s t : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
    inner_disk).pairedComplex.CutSeam
      ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
        inner_disk).pairedComplex.processedParentRetain
        (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
          inner_disk beta acute).selection S)}
  {side flag other nextFlag : Bool}
  (A : K.CompatibleComparisonFiniteChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered s side flag)
  (B : K.CompatibleComparisonFiniteChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered t other nextFlag)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}
local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

open Classical in
/-- Distinct original cut-bank labels force disjoint actual fine-bank labels in both
orientations. The conclusion is derived from regular original metric copies. -/
theorem CompatibleComparisonFiniteChainModel.separated
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other) :
    ∀ i j, A.chain.point i ≠ B.chain.point j ∧
      A.chain.point i ≠ (NewAt[S,later,ordered]).pairedComplex.boundaryTurn
        NewRetainAt[S,later,ordered] (B.chain.point j) := by
  intro i j
  have apart : ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
      NewRetainAt[S,later,ordered] (A.chain.point i)).1 ≠
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndEquiv
        NewRetainAt[S,later,ordered] (B.chain.point j)).1 := by
    intro same_bank
    let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    let first_clock := closedUnitIntervalLineMap (A.lower i) (A.upper i) (A.forward i).le half
    have interior_time := closedUnitIntervalLineMap_strict (A.lower i) (A.upper i) (A.forward i)
      half ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 / 2 : ℝ) < 1 by norm_num⟩
    have member : (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath
        (A.chain.point i) half ∈
        Set.range ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath
          (B.chain.point j)) := by
      rw [(NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_range, ← same_bank]
      exact ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath_range
        (A.chain.point i)).subset ⟨half, rfl⟩
    obtain ⟨v, at_point⟩ := member
    let last_clock := closedUnitIntervalLineMap (B.lower j) (B.upper j) (B.forward j).le v
    have actual := (A.matching i half).symm.trans (at_point.symm.trans (B.matching j v))
    have map_first := K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag] first_clock
    have map_last := K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,t,other,nextFlag] last_clock
    have original_image := map_first.symm.trans
      ((congrArg NewMapAt[S,later,ordered] actual).trans map_last)
    have below := K.compatibleMeshProcessed_directedCutBank_height_lt compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S s side flag first_clock interior_time
    have original := K.compatibleMeshProcessedWholeMap_injective_at compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S _ below _ original_image
    have first_parameter := (T).pairedComplex.directedBoundaryPath_from_bank
      ((T).pairedComplex.cutBank RetainAt[S] s side) flag first_clock
    have last_parameter := (T).pairedComplex.directedBoundaryPath_from_bank
      ((T).pairedComplex.cutBank RetainAt[S] t other) nextFlag last_clock
    exact (T).pairedComplex.bankMap_ne_of_ne RetainAt[S] different
      ((T).pairedComplex.bankParameterFromEnd
        ((T).pairedComplex.cutBank RetainAt[S] s side) flag first_clock)
      ((T).pairedComplex.bankParameterFromEnd
        ((T).pairedComplex.cutBank RetainAt[S] t other) nextFlag last_clock)
      ((T).pairedComplex.bankParameterFromEnd_nonvertex
        ((T).pairedComplex.cutBank RetainAt[S] s side) flag first_clock
        interior_time.1 interior_time.2)
      (first_parameter.symm.trans (original.trans last_parameter))
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
/-- The first fine vertex is the literal lifted original starting endpoint. -/
theorem CompatibleComparisonFiniteChainModel.first_point :
    (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        A.chain.first) = LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] 0 :=
  (A.vertexPoint 0).trans
    (congrArg LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] (Subtype.ext A.start_time))

open Classical in
/-- The last fine vertex is the literal lifted original final endpoint. -/
theorem CompatibleComparisonFiniteChainModel.last_point :
    (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
          A.chain.last)) = LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] 1 :=
  ((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_last A.chain A.lower A.upper
    A.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] A.matching (Fin.last A.length)).trans
    (congrArg LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] (Subtype.ext A.finish_time))

open Classical in
/-- An original intrinsic endpoint join determines the actual boundary successor
between its two constructed fine blocks. No fine endpoint or successor is supplied. -/
theorem CompatibleComparisonFiniteChainModel.joined
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other)
    (corner : (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,t,other,nextFlag]) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryMate NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        A.chain.last) = B.chain.first := by
  have source_join : (T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] 1 =
      (T).pairedComplex.directedBoundaryPath OldEndAt[S,t,other,nextFlag] 0 := by
    rw [(T).pairedComplex.directedBoundaryPath_one, (T).pairedComplex.directedBoundaryPath_zero]
    exact congrArg ((T).pairedComplex.vertexPoint RetainAt[S]) corner
  have first_map := (congrArg NewMapAt[S,later,ordered] A.last_point).trans
    (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] 1)
  have last_map := (congrArg NewMapAt[S,later,ordered] B.first_point).trans
    (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered OldEndAt[S,t,other,nextFlag] 0)
  have same_map := first_map.trans ((congrArg MapAt[S] source_join).trans last_map.symm)
  have old_height := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S]
    ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] (A.upper (Fin.last A.length)))
  rw [M.clip_eq_sublevel, neg_neg] at old_height
  have below := (congrArg (fun z : Space =>
    (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z))
      (A.last (Fin.last A.length))).trans_le old_height
  have points := K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered _
    (below.trans_lt ordered) _ same_map
  have vertices := (NewAt[S,later,ordered]).pairedComplex.vertexPoint_injective
    NewRetainAt[S,later,ordered] points
  have distinct : B.chain.first ≠
      (NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        A.chain.last := by
    intro same
    have reversed := congrArg
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]) same
    rw [(NewAt[S,later,ordered]).pairedComplex.boundaryTurn_involutive] at reversed
    exact (A.separated B different (Fin.last A.length) 0).2 reversed.symm
  exact ((NewAt[S,later,ordered]).pairedComplex.exists_unique_other_boundaryEnd
    NewRetainAt[S,later,ordered]
    ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] A.chain.last)
    |>.unique ⟨distinct, vertices.symm⟩
      ((NewAt[S,later,ordered]).pairedComplex.boundaryMate_spec NewRetainAt[S,later,ordered] _)
    ).symm

open Classical in
/-- Concatenate constructed fine blocks using only original bank labels and their
original intrinsic endpoint join. -/
def CompatibleComparisonFiniteChainModel.concat
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other)
    (corner : (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,t,other,nextFlag]) :
    ((NewAt[S,later,ordered]).pairedComplex.boundarySystem NewRetainAt[S,later,ordered]).Chain
      (A.length + B.length + 1) :=
  A.chain.concat B.chain (A.separated B different) (A.joined B different corner)

open Classical in
@[simp] theorem CompatibleComparisonFiniteChainModel.concat_first
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other)
    (corner : (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,t,other,nextFlag]) :
    (A.concat B different corner).first = A.chain.first :=
  A.chain.concat_first B.chain _ _

open Classical in
@[simp] theorem CompatibleComparisonFiniteChainModel.concat_last
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other)
    (corner : (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,t,other,nextFlag]) :
    (A.concat B different corner).last = B.chain.last :=
  A.chain.concat_last B.chain _ _

open Classical in
/-- Concatenated actual fine blocks retain exactly both entire original bank images,
including the literal joined endpoint copy. -/
theorem CompatibleComparisonFiniteChainModel.concat_trace
    (different : (T).pairedComplex.cutBank RetainAt[S] s side ≠
      (T).pairedComplex.cutBank RetainAt[S] t other)
    (corner : (T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]) =
      (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,t,other,nextFlag]) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace (A.concat B different corner) =
      Set.range LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] ∪
        Set.range LiftAt[S,later,ordered,OldEndAt[S,t,other,nextFlag]] :=
  ((NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace_concat A.chain B.chain
    (A.separated B different) (A.joined B different corner)).trans
    (congrArg₂ (fun x y => x ∪ y) A.trace.symm B.trace.symm)

end Unfoldings.ConvexRoof
