module

public import Unfoldings.Roof.CompatibleComparisonFinitePathAssembly
public import Unfoldings.Roof.CompatibleComparisonChainHeading
public import Unfoldings.Roof.CompatibleComparisonFiniteFollows
public import Unfoldings.Complex.DirectedBankChain
public import Unfoldings.Geometry.RadialMarginSubdivision
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Geometry.RadialChain

/-! Complete actual comparison refinements preserve every original compatible routing step. -/

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

local instance comparisonChainFollowsIndexFintype : Fintype (T).Index :=
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
local instance comparisonChainFollowsNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonChainFollowsWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S

open Classical in
/-- Complete actual bank coverage preserves the original compatible routing step at every bank. -/
theorem compatibleMeshProcessedComparison_chain_follows
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) {m n : ℕ}
    (original : ((T).pairedComplex.boundarySystem RetainAt[S]).Chain m)
    (label : Fin (m + 1) → (T).pairedComplex.DirectedCutBank RetainAt[S])
    (named : ∀ i, (label i).start = original.point i)
    (fine : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (covered : ∀ p, (∃ j, fine.point j = p) ↔ ∃ i j,
      (K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered
        (label i).seam (label i).side (label i).flag).chain.point j = p)
    (follows : R.Follows ((T).pairedFolding.projectedBoundaryChain original)) :
    R.Follows ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain fine) := by
  intro j
  obtain ⟨i, k, same⟩ := (covered (fine.point j)).mp ⟨j, rfl⟩
  let D := K.compatibleMeshProcessedComparisonFiniteChainModel compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered
    (label i).seam (label i).side (label i).flag
  change D.chain.point k = fine.point j at same
  have original_step : R.FollowsStep
      (Cap.horizontal ((T).pairedFolding.boundaryPosition (original.point i)))
      (Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn RetainAt[S] (original.point i)))) :=
    Eq.mp (congrArg₂ R.FollowsStep
      ((T).pairedFolding.projectedBoundaryChain_vertex_castSucc original i)
      ((T).pairedFolding.projectedBoundaryChain_vertex_succ original i)) (follows i)
  have labelled : R.FollowsStep
      (Cap.horizontal ((T).pairedFolding.boundaryPosition (label i).start))
      (Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn RetainAt[S] (label i).start))) :=
    Eq.mpr (congrArg (fun p => R.FollowsStep
      (Cap.horizontal ((T).pairedFolding.boundaryPosition p))
      (Cap.horizontal ((T).pairedFolding.boundaryPosition
        ((T).pairedComplex.boundaryTurn RetainAt[S] p)))) (named i)) original_step
  have first := ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc
    D.chain k).trans ((congrArg (fun p => Cap.horizontal
      ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition p)) same).trans
      ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_castSucc fine j).symm)
  have last := ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_succ
    D.chain k).trans ((congrArg (fun p => Cap.horizontal
      ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn
          NewRetainAt[S,later,ordered] p))) same).trans
      ((NewAt[S,later,ordered]).pairedFolding.projectedBoundaryChain_vertex_succ fine j).symm)
  exact Eq.mp (congrArg₂ R.FollowsStep first last) (D.follows labelled k)

end Unfoldings.ConvexRoof
