module

public import Unfoldings.Roof.CompatibleComparisonFiniteChainModel
public import Unfoldings.Roof.CompatibleStepSubsegments
public import Unfoldings.Polyhedron.ProjectedBankInterpolation
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Complex.BoundaryChainIntervalParameters
public import Unfoldings.Polyhedron.SubintervalBankVectors
public import Unfoldings.Complex.BoundaryChainAperture
public import Unfoldings.Geometry.PolygonalLength

/-! Constructed finite comparison banks follow the same original compatible routing steps. -/

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

local instance comparisonFiniteFollowsModelIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteFollowsModelNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteFollowsModelWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- Ordered whole-bank correspondence preserves actual compatible routing, not just its carrier. -/
theorem CompatibleComparisonFiniteChainModel.follows
    (step : R.FollowsStep (Cap.horizontal ((T).pairedFolding.boundaryPosition
      OldEndAt[S,s,side,flag])) (Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag])))) :
    R.Follows ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain) := by
  intro i
  have smaller := R.followsStep_subsegment step (D.lower i) (D.upper i) (D.forward i).le
  have first : ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain).vertex
      i.castSucc = AffineMap.lineMap
        (Cap.horizontal ((T).pairedFolding.boundaryPosition OldEndAt[S,s,side,flag]))
        (Cap.horizontal ((T).pairedFolding.boundaryPosition
          ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))) (D.lower i).val :=
    ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc D.chain i).trans
      ((congrArg Cap.horizontal (D.first i)).trans
        ((T).pairedFolding.directedBoundaryPath_horizontal_lineMap _ _))
  have last : ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain D.chain).vertex
      i.succ = AffineMap.lineMap
        (Cap.horizontal ((T).pairedFolding.boundaryPosition OldEndAt[S,s,side,flag]))
        (Cap.horizontal ((T).pairedFolding.boundaryPosition
          ((T).pairedComplex.boundaryTurn RetainAt[S] OldEndAt[S,s,side,flag]))) (D.upper i).val :=
    ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_succ D.chain i).trans
      ((congrArg Cap.horizontal (D.last i)).trans
        ((T).pairedFolding.directedBoundaryPath_horizontal_lineMap _ _))
  exact Eq.mpr (congrArg₂ R.FollowsStep first last) smaller

end Unfoldings.ConvexRoof
