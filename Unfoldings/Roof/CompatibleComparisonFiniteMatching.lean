module

public import Unfoldings.Roof.CompatibleComparisonFiniteVertices
public import Unfoldings.Roof.CompatibleProcessedBankInterior
public import Unfoldings.Roof.CompatibleProcessedComparisonFiber
public import Unfoldings.Polyhedron.DirectedBankSubinterval

/-! One regular contact fixes the entire actual comparison bank on its original finite-bank side. -/

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

local instance comparisonFiniteMatchingIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteMatchingNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteMatchingWholeFintype : Fintype W.Index := W.finiteIndex

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
/-- A forward comparison bank with the original spatial endpoints is exactly the
original finite-bank restriction once one regular contact fixes its intrinsic side.
The conclusion retains every point and both endpoint copies. -/
theorem compatibleMeshProcessedComparison_directedBank_finiteCutBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.CutSeam RetainAt[S]) (side flag : Bool)
    (p : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
    (first last : unitInterval) (forward : first.val < last.val)
    (initial : (NewAt[S,later,ordered]).pairedFolding.boundaryPosition p =
      (T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] first))
    (final : (NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] p) =
      (T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] last))
    (t : unitInterval) (interior_contact : t ∈ Set.Ioo (0 : unitInterval) 1)
    (contact : (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p t =
      LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
        (closedUnitIntervalLineMap first last forward.le t)) :
    ∀ u : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u =
      LiftAt[S,later,ordered,OldEndAt[S,s,side,flag]]
        (closedUnitIntervalLineMap first last forward.le u) := by
  let clock := closedUnitIntervalLineMap first last forward.le
  let curve (u : unitInterval) := NewMapAt[S,later,ordered]
    ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u)
  have continuous_curve : Continuous curve :=
    (K.compatibleMeshProcessedComparisonWholeMap_lipschitz compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered).continuous.comp
      ((NewAt[S,later,ordered]).pairedComplex.continuous_directedBoundaryPath p)
  have physical (u : unitInterval) :=
    (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered
        ((NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath p u)).trans
      (((NewAt[S,later,ordered]).pairedFolding.directedBoundaryPath_lineMap p u).trans
        ((congrArg₂ (fun x y : Space => AffineMap.lineMap x y u.val) initial final).trans
          ((T).pairedFolding.directedBoundaryPath_subinterval OldEndAt[S,s,side,flag]
            first last forward.le u).symm))
  have named_contact := (congrArg NewMapAt[S,later,ordered] contact).trans
    (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered OldEndAt[S,s,side,flag] (clock t))
  have matched_paths := K.compatibleMeshProcessedCutBank_eq_of_subinterval_contact compact nonempty
    R no_boundary level higher M positive inner_disk beta acute W S s side flag first last forward
    curve continuous_curve physical t interior_contact named_contact
  intro u
  have map_lift := K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered
    OldEndAt[S,s,side,flag] (clock u)
  have original_height := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S]
    ((T).pairedComplex.directedBoundaryPath OldEndAt[S,s,side,flag] (clock u))
  rw [M.clip_eq_sublevel, neg_neg] at original_height
  have folded := K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered
    OldEndAt[S,s,side,flag] (clock u)
  have below := (congrArg (fun z : Space =>
    (K.clippedExtension slopes compact nonempty).height (Cap.horizontal z)) folded).trans_le
      original_height
  exact (K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered _ (below.trans_lt ordered) _
      (map_lift.trans (matched_paths u).symm)).symm

end Unfoldings.ConvexRoof
