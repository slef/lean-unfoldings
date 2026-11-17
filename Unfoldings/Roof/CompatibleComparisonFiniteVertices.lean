module

public import Unfoldings.Roof.CompatibleComparisonPrescribedGeometry
public import Unfoldings.Geometry.SpatialEnvelopeCutBankParameters

/-! Original finite-bank endpoint copies are actual vertices in every larger comparison mesh. -/

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

local instance comparisonFiniteVerticesIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteVerticesNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteVerticesWholeFintype : Fintype W.Index := W.finiteIndex

local notation "BankAt[" S "," L "," h "," s "," removed "," side "," flag "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h
    (Equiv.symm (TriangleComplex.boundaryEndEquiv
      (SpatialEnvelope.Triangulation.pairedComplex
        (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) RetainAt[S])
      (TriangleComplex.cutBank (SpatialEnvelope.Triangulation.pairedComplex
        (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
        RetainAt[S] ⟨s, removed⟩ side, flag))

open Classical in
/-- Every lifted point of either original finite cut bank lies on its original
projected edge segment, including both endpoint copies. -/
theorem compatibleMeshProcessedComparisonFiniteCutBank_mem_segment
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (side flag : Bool) (u : unitInterval) :
    Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      (BankAt[S,later,ordered,s,removed,side,flag] u)) ∈
      segment ℝ (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
          ((T).pairedComplex.left s).edge)
        (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
          (Triangle.next ((T).pairedComplex.left s).edge)) := by
  let bank := (T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side
  let p := ((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm (bank, flag)
  have parameter := (T).pairedComplex.directedBoundaryPath_from_bank bank flag u
  have folded := (K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered p u).trans
      (congrArg ((T).pairedFolding.toSpace RetainAt[S]) parameter)
  exact (congrArg (fun z : Space => Cap.horizontal z ∈
      ((T).projectedTriangle ((T).pairedComplex.left s).face).edge
        ((T).pairedComplex.left s).edge) folded).mpr
    ((T).toTriangulation.horizontal_cutBank_mem_left_edge RetainAt[S] ⟨s, removed⟩ side
      ((T).pairedComplex.bankParameterFromEnd bank flag u))

open Classical in
/-- Both original endpoint copies of each lifted finite cut bank are actual comparison
vertices, on either bank and with either original starting orientation. -/
theorem exists_compatibleMeshProcessedComparisonFiniteCutBank_endpoint_vertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (side flag : Bool) (u : unitInterval) (endpoint : u.val = 0 ∨ u.val = 1) :
    ∃ vertex : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] vertex =
        BankAt[S,later,ordered,s,removed,side,flag] u := by
  let bank := (T).pairedComplex.cutBank RetainAt[S] ⟨s, removed⟩ side
  let p := ((T).pairedComplex.boundaryEndEquiv RetainAt[S]).symm (bank, flag)
  have parameter := (T).pairedComplex.directedBoundaryPath_from_bank bank flag u
  have folded := (K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered p u).trans
      (congrArg ((T).pairedFolding.toSpace RetainAt[S]) parameter)
  have vertex := (T).pairedComplex.bankParameterFromEnd_isVertex_of_endpoint bank flag u endpoint
  have ends := (T).toTriangulation.horizontal_cutBank_endpoint RetainAt[S] ⟨s, removed⟩ side
    ((T).pairedComplex.bankParameterFromEnd bank flag u) vertex
  let pair : {p // p ∈ PairsAt[S,later]} :=
    ⟨(((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
        ((T).pairedComplex.left s).edge,
      ((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
        (Triangle.next ((T).pairedComplex.left s).edge)),
      by
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨s, removed⟩, Finset.mem_univ _, ?_⟩
        rw [(T).toTriangulation.roof_projectedTriangle conforming inside]⟩
  exact K.exists_compatibleMeshProcessedComparison_pair_endpoint_vertex compact nonempty R
    no_boundary level higher M positive inner_disk beta acute S later ordered pair _
      (ends.imp ((congrArg Cap.horizontal folded).trans ·)
        ((congrArg Cap.horizontal folded).trans ·))

open Classical in
/-- A nonvertex point of either lifted original bank determines a whole actual fine
bank in the original edge order, retaining the literal intrinsic contact copy. -/
theorem exists_compatibleMeshProcessedComparison_forward_finiteCutBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (s : (T).pairedComplex.Seam) (removed : s ∉ RetainAt[S])
    (side flag : Bool) (u : unitInterval)
    (regular : ∀ v : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered],
      BankAt[S,later,ordered,s,removed,side,flag] u ≠
        (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered] v) :
    ∃ (q : (NewAt[S,later,ordered]).pairedComplex.BoundaryEnd NewRetainAt[S,later,ordered])
      (first last : unitInterval), first.val < last.val ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition q) =
        AffineMap.lineMap
          (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
            ((T).pairedComplex.left s).edge)
          (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
            (Triangle.next ((T).pairedComplex.left s).edge)) first.val ∧
      Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        ((NewAt[S,later,ordered]).pairedComplex.boundaryTurn NewRetainAt[S,later,ordered] q)) =
        AffineMap.lineMap
          (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
            ((T).pairedComplex.left s).edge)
          (((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
            (Triangle.next ((T).pairedComplex.left s).edge)) last.val ∧
      ∃ v : unitInterval, (NewAt[S,later,ordered]).pairedComplex.directedBoundaryPath q v =
        BankAt[S,later,ordered,s,removed,side,flag] u := by
  obtain ⟨p, t, at_point⟩ :=
    K.exists_directedBank_at_compatibleMeshProcessedComparisonFiniteCutBank compact nonempty R
      no_boundary level higher M positive inner_disk beta acute W S later ordered s removed
      side flag u
  let pair : {p // p ∈ PairsAt[S,later]} :=
    ⟨(((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
        ((T).pairedComplex.left s).edge,
      ((T).projectedTriangle ((T).pairedComplex.left s).face).vertex
        (Triangle.next ((T).pairedComplex.left s).edge)),
      by
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨s, removed⟩, Finset.mem_univ _, ?_⟩
        rw [(T).toTriangulation.roof_projectedTriangle conforming inside]⟩
  have on_segment := K.compatibleMeshProcessedComparisonFiniteCutBank_mem_segment compact nonempty
    R no_boundary level higher M positive inner_disk beta acute W S later ordered s removed side
      flag u
  obtain ⟨q, first, last, forward, initial, final, v, same⟩ :=
    K.exists_compatibleMeshProcessedComparison_forward_pair_bank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute S later ordered pair p t
      (fun vertex equal => regular vertex (at_point.symm.trans equal))
      ((congrArg (fun z => Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] z) ∈ segment ℝ pair.val.1 pair.val.2) at_point).mpr on_segment)
  exact ⟨q, first, last, forward, initial, final, v, same.trans at_point⟩

end Unfoldings.ConvexRoof
