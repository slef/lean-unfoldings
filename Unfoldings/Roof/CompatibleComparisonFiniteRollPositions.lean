module

public import Unfoldings.Roof.CompatibleComparisonFiniteChainTurns
public import Unfoldings.Geometry.ComplexAffineInterpolation
public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.FiniteInterpolation

/-! Exact original pointwise positions and ordered images of actual finite-bank rolls. -/

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

local instance comparisonFiniteRollPositionsIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteRollPositionsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteRollPositionsWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- All original fine-vertex times, including both endpoints, in their actual chain order. -/
def CompatibleComparisonFiniteChainModel.time :
    Fin (D.length + 2) → Set.Icc (0 : ℝ) 1 :=
  TriangleComplex.boundaryChainIntervalTime D.lower D.upper

open Classical in
@[simp] theorem CompatibleComparisonFiniteChainModel.time_castSucc (i : Fin (D.length + 1)) :
    D.time i.castSucc = D.lower i :=
  TriangleComplex.boundaryChainIntervalTime_castSucc D.lower D.upper i

open Classical in
@[simp] theorem CompatibleComparisonFiniteChainModel.time_last :
    D.time (Fin.last (D.length + 1)) = D.upper (Fin.last D.length) :=
  TriangleComplex.boundaryChainIntervalTime_last D.lower D.upper

open Classical in
theorem CompatibleComparisonFiniteChainModel.time_succ (i : Fin (D.length + 1)) :
    D.time i.succ = D.upper i :=
  (NewAt[S,later,ordered]).pairedComplex.boundaryChainIntervalTime_succ D.chain D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
    (K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag]).injective
    D.matching i

open Classical in
theorem CompatibleComparisonFiniteChainModel.time_strictMono : StrictMono D.time :=
  (NewAt[S,later,ordered]).pairedComplex.strictMono_boundaryChainIntervalTime D.chain
    D.lower D.upper
    D.forward LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
    (K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered
      OldEndAt[S,s,side,flag]).injective
    D.matching

open Classical in
/-- Every rolled fine vertex has its exact original arclength coordinate. -/
theorem CompatibleComparisonFiniteChainModel.rolledVertex (i : Fin (D.length + 2)) :
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).vertex i =
      (((D.time i).val *
        ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ : ℝ) : ℂ) := by
  let roll := (NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain
  refine Fin.induction ?_ (fun i previous => ?_) i
  · change roll.vertex 0 = _
    change (PolygonalChain.ofHeadings (0 : ℂ) _ _).vertex 0 = _
    rw [PolygonalChain.ofHeadings_start]
    rw [show (0 : Fin (D.length + 2)) = (0 : Fin (D.length + 1)).castSucc from rfl,
      D.time_castSucc]
    rw [D.start_time, zero_mul, Complex.ofReal_zero]
  · have step := D.rolledEdge i
    change roll.vertex i.succ - roll.vertex i.castSucc = _ at step
    have position := eq_add_of_sub_eq step
    rw [previous] at position
    apply position.trans
    rw [D.time_castSucc, D.time_succ]
    push_cast
    ring

open Classical in
/-- Every point of every actual rolled fine bank retains its original interval parameter. -/
theorem CompatibleComparisonFiniteChainModel.rolledPoint
    (i : Fin (D.length + 1)) (u : unitInterval) :
    ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).point i u =
      (((closedNonnegativeIntervalLineMap (D.lower i).val (D.upper i).val 1
        (D.lower i).property.1 (D.forward i).le (D.upper i).property.2 u).val *
        ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ : ℝ) : ℂ) := by
  rw [PolygonalChain.point, D.rolledVertex, D.rolledVertex, D.time_castSucc, D.time_succ]
  apply (complex_lineMap_real_mul _ _ _ _).trans
  apply congrArg (fun z : ℝ =>
    ((z * ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ : ℝ) : ℂ))
  rw [AffineMap.lineMap_apply_module']
  change u.val * ((D.upper i).val - (D.lower i).val) + (D.lower i).val =
    (D.lower i).val + u.val * ((D.upper i).val - (D.lower i).val)
  ring

open Classical in
/-- The whole actual rolled path is exactly the original closed arclength interval,
including both endpoints. Every bank point is retained in its original time order. -/
theorem CompatibleComparisonFiniteChainModel.rolledPath_range :
    Set.range ((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).path =
      Set.range (fun t : Set.Icc (0 : ℝ) 1 =>
        ((t.val * ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ : ℝ) : ℂ)) := by
  let roll := (NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain
  have embedded := K.compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding compact
    nonempty R no_boundary level higher M positive inner_disk beta acute W S later ordered
    OldEndAt[S,s,side,flag]
  apply Set.Subset.antisymm
  · rintro x ⟨u, rfl⟩
    obtain ⟨i, v, at_point⟩ := roll.path_point_covered (by omega) u
    let t := closedNonnegativeIntervalLineMap (D.lower i).val (D.upper i).val 1
      (D.lower i).property.1 (D.forward i).le (D.upper i).property.2 v
    exact ⟨t, (at_point.trans (D.rolledPoint i v)).symm⟩
  · rintro x ⟨t, rfl⟩
    have covered := D.trace.subset ⟨t, rfl⟩
    rw [(NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace_eq_union_paths] at covered
    obtain ⟨i, v, at_point⟩ := Set.mem_iUnion.mp covered
    have parameter := embedded.injective ((D.matching i v).symm.trans at_point)
    have value := congrArg (fun z : Set.Icc (0 : ℝ) 1 =>
      ((z.val * ‖(T).pairedFolding.germDirection (OldEndAt[S,s,side,flag]).val‖ : ℝ) : ℂ)) parameter
    rw [roll.path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, v, (D.rolledPoint i v).trans value⟩)

open Classical in
/-- Rolled fine vertices occur in strict original order on the positive real axis. -/
theorem CompatibleComparisonFiniteChainModel.rolledVertex_re_strictMono :
    StrictMono (fun i =>
      (((NewAt[S,later,ordered]).pairedComplex.boundaryChainRoll D.chain).vertex i).re) := by
  intro i j before
  dsimp only
  rw [D.rolledVertex, D.rolledVertex, Complex.ofReal_re, Complex.ofReal_re]
  exact mul_lt_mul_of_pos_right (D.time_strictMono before)
    (norm_pos_iff.mpr ((T).pairedFolding.germDirection_ne_zero (OldEndAt[S,s,side,flag]).val))


end Unfoldings.ConvexRoof
