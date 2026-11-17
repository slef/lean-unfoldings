module

public import Unfoldings.Roof.CompatibleComparisonFiniteChains
public import Unfoldings.Complex.BoundaryChainIntervalParameters
public import Unfoldings.Polyhedron.SubintervalBankVectors
public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.PolygonalLength

/-! Original interval partitions and exact vectors of constructed finite comparison chains. -/

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

local instance comparisonFiniteChainModelIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteChainModelNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteChainModelWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- The constructed finite comparison chain and its exact original bank intervals.
All fields are derived by the constructor below. -/
structure CompatibleComparisonFiniteChainModel
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool) where
  length : ℕ
  chain : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
    NewRetainAt[S,later,ordered]).Chain length
  lower : Fin (length + 1) → unitInterval
  upper : Fin (length + 1) → unitInterval
  forward : ∀ i, (lower i).val < (upper i).val
  matching : ∀ i u, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (chain.point i) u =
    LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
      (closedUnitIntervalLineMap (lower i) (upper i) (forward i).le u)
  trace : Set.range LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] =
    (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace chain
  start_time : (lower 0).val = 0
  finish_time : (upper (Fin.last length)).val = 1

open Classical in
/-- Construct the fine chain and its original time partition for either original bank
side and orientation, without ordering, endpoint or matching certificates. -/
def compatibleMeshProcessedComparisonFiniteChainModel
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool) :
    K.CompatibleComparisonFiniteChainModel compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered s side flag := by
  apply Classical.choice
  obtain ⟨n, chain, index, named, trace, initial, terminal⟩ :=
    K.exists_compatibleMeshProcessedComparisonFiniteBank_chain compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered s side flag
  have choices (i : Fin (n + 1)) := (index i).property
  choose lower upper forward matching using choices
  have matched_paths : ∀ i u,
      (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath (chain.point i) u =
        LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
          (closedUnitIntervalLineMap (lower i) (upper i) (forward i).le u) := by
    intro i u
    rw [named i]
    exact matching i u
  have embedded := K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty
    R no_boundary level higher M positive inner_disk beta acute W S later ordered
    OldEndAt[S,s,side,flag]
  refine ⟨⟨n, chain, lower, upper, forward, matched_paths, trace, ?_, ?_⟩⟩
  · exact congrArg Subtype.val (embedded.injective
      (((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_first chain lower upper
        forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
        matched_paths 0).symm.trans initial))
  · exact congrArg Subtype.val (embedded.injective
      (((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_last chain lower upper
        forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] matched_paths (Fin.last n)
        ).symm.trans terminal))

variable {S : (K.compatibleMeshForest compact nonempty R no_boundary level higher M
    positive inner_disk beta acute).parents.ParentFrontier}
  {later : ℝ} {ordered : level < later}
  {s : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
    inner_disk).pairedComplex.CutSeam
      ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
        inner_disk).pairedComplex.processedParentRetain
        (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
          inner_disk beta acute).selection S)}
  {side flag : Bool}
  (D : K.CompatibleComparisonFiniteChainModel compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered s side flag)

variable {K compact nonempty R no_boundary level higher M positive inner_disk beta acute W}
open Classical in
/-- Adjacent actual finite banks share one literal original time parameter. -/
theorem CompatibleComparisonFiniteChainModel.joins (i : Fin D.length) :
    D.upper i.castSucc = D.lower i.succ :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_joins D.chain D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
    (K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag]).injective
    D.matching i

open Classical in
/-- The actual finite chain moves strictly forward in original time. -/
theorem CompatibleComparisonFiniteChainModel.strictMono : StrictMono (fun i => (D.lower i).val) :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_strictMono D.chain D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] D.matching
    (K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag]).injective

open Classical in
/-- Every internal fine hinge is strictly between the original endpoints. -/
theorem CompatibleComparisonFiniteChainModel.internal (i : Fin D.length) :
    0 < (D.lower i.succ).val ∧ (D.lower i.succ).val < 1 :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_internal D.chain D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] D.matching
    (K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag]).injective
    i

open Classical in
/-- Actual chain vertices retain their literal original bank copies at the recorded times. -/
theorem CompatibleComparisonFiniteChainModel.vertexPoint (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        (D.chain.point i)) = LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] (D.lower i) :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_first D.chain D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] D.matching i

open Classical in
/-- Actual first endpoints retain their full original spatial positions. -/
theorem CompatibleComparisonFiniteChainModel.first (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedFolding.boundaryPosition (D.chain.point i) =
      (T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] (D.lower i)) :=
  (congrArg ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered])
    (D.vertexPoint i)).trans
      (K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered
        OldEndAt[S,s,side,flag] (D.lower i))

open Classical in
/-- Actual final endpoints retain their full original spatial positions. -/
theorem CompatibleComparisonFiniteChainModel.last (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedFolding.boundaryPosition
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        (D.chain.point i)) =
      (T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] (D.upper i)) :=
  (congrArg ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered])
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChain_interval_last D.chain D.lower D.upper
      D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]] D.matching i)).trans
      (K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered
        OldEndAt[S,s,side,flag] (D.upper i))

open Classical in
/-- Every forward fine edge keeps its exact original full spatial bank velocity. -/
theorem CompatibleComparisonFiniteChainModel.spatialVector (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedFolding.germDirection (D.chain.point i).val =
      ((D.upper i).val - (D.lower i).val) •
        (T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val :=
  (NewAt[S,later,ordered]).pairedFolding.germDirection_eq_bank_subinterval (T).pairedFolding
    (D.chain.point i) OldEndAt[S,s,side,flag] (D.lower i) (D.upper i) (D.first i) (D.last i)

open Classical in
/-- Each fine-edge length is its original time increment times original spatial speed. -/
theorem CompatibleComparisonFiniteChainModel.bankLength (i : Fin (D.length + 1)) :
    (NewAt[S,later,ordered]).pairedComplex.boundaryBankLength (D.chain.point i) =
      ((D.upper i).val - (D.lower i).val) *
        ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ := by
  rw [(NewAt[S,later,ordered]).pairedFolding.boundaryBankLength_eq_germDirection_norm,
    D.spatialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (D.forward i).le)]

open Classical in
/-- The complete original time interval is partitioned without omissions or repetitions. -/
theorem CompatibleComparisonFiniteChainModel.sum_time :
    (∑ i, ((D.upper i).val - (D.lower i).val)) = 1 := by
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun i : Fin (D.length + 1) => (D.upper i).val),
    Fin.sum_univ_succ (fun i : Fin (D.length + 1) => (D.lower i).val)]
  have same : (∑ i : Fin D.length, (D.upper i.castSucc).val) =
      ∑ i : Fin D.length, (D.lower i.succ).val :=
    Finset.sum_congr rfl (fun i _ => congrArg Subtype.val (D.joins i))
  rw [same, D.finish_time, D.start_time]
  ring

open Classical in
/-- The complete actual fine chain rolls to precisely the original bank arclength. -/
theorem CompatibleComparisonFiniteChainModel.rolledLength :
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).projectedLength =
      ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ := by
  simp only [PolygonalChain.projectedLength,
    TriangleComplex.boundaryChainRoll_edge_length, D.bankLength, ← Finset.sum_mul, D.sum_time,
    one_mul]

end Unfoldings.ConvexRoof
