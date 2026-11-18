module

public import Unfoldings.Roof.CompatibleComparisonBankOriginalFans
public import Unfoldings.Roof.CompatibleComparisonFiniteBlockJoins

/-! Actual comparison-block endpoints retain exact original cut vertices and fan angles. -/

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

local instance comparisonFiniteOriginalTurnsIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteOriginalTurnsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteOriginalTurnsWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "OriginalVertexAt[" S "," L "," h "," c "]" =>
  K.compatibleMeshProcessedComparisonOriginalVertex compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h c

open Classical in
/-- The constructed block starts at the corresponding original full-mesh cut-side vertex. -/
theorem CompatibleComparisonFiniteChainModel.first_original_vertex :
    (NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
      D.chain.first = OriginalVertexAt[S,later,ordered,
        (T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,s,side,flag]] := by
  apply (NewAt[S,later,ordered]).pairedComplex.vertexPoint_injective NewRetainAt[S,later,ordered]
  exact D.first_point.trans
    (K.compatibleMeshProcessedComparisonFiniteBank_eq_originalVertex compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] 0
      ((T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,s,side,flag])
      ((T).pairedComplex.directedBoundaryPath_zero OldEndAt[S,s,side,flag]))

open Classical in
/-- The constructed block finishes at the corresponding original full-mesh cut-side vertex. -/
theorem CompatibleComparisonFiniteChainModel.last_original_vertex :
    (NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        D.chain.last) = OriginalVertexAt[S,later,ordered,
          (T).pairedComplex.boundaryEndVertex RetainAt[S]
            ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag])] := by
  apply (NewAt[S,later,ordered]).pairedComplex.vertexPoint_injective NewRetainAt[S,later,ordered]
  exact D.last_point.trans
    (K.compatibleMeshProcessedComparisonFiniteBank_eq_originalVertex compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] 1
      ((T).pairedComplex.boundaryEndVertex RetainAt[S]
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))
      ((T).pairedComplex.directedBoundaryPath_one OldEndAt[S,s,side,flag]))

open Classical in
/-- Every original internal junction keeps its exact old angle at the actual new block start. -/
theorem CompatibleComparisonFiniteChainModel.first_original_angle
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition OldEndAt[S,s,side,flag])) < level) :
    (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        D.chain.first) = (T).pairedComplex.totalAngle RetainAt[S]
          ((T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,s,side,flag]) :=
  K.compatibleMeshProcessedComparisonFiniteBank_original_totalAngle compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] 0
    ((T).pairedComplex.boundaryEndVertex RetainAt[S] OldEndAt[S,s,side,flag])
    ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
      D.chain.first) ((T).pairedComplex.directedBoundaryPath_zero OldEndAt[S,s,side,flag])
    D.first_point below

open Classical in
/-- The last bank endpoint retains its original angle whenever it lies below the old rim. -/
theorem CompatibleComparisonFiniteChainModel.last_original_angle
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))) < level) :
    (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
          D.chain.last)) = (T).pairedComplex.totalAngle RetainAt[S]
          ((T).pairedComplex.boundaryEndVertex RetainAt[S]
            ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag])) :=
  K.compatibleMeshProcessedComparisonFiniteBank_original_totalAngle compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] 1
    ((T).pairedComplex.boundaryEndVertex RetainAt[S]
      ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))
    ((NewAt[S,later,ordered]).pairedComplex.boundaryEndVertex NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered]
        D.chain.last))
    ((T).pairedComplex.directedBoundaryPath_one OldEndAt[S,s,side,flag]) D.last_point below

end Unfoldings.ConvexRoof
