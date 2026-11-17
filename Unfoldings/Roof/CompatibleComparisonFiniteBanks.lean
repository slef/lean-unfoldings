module

public import Unfoldings.Roof.CompatibleProcessedComparisonCharts
public import Unfoldings.Roof.CompatibleProcessedBankMetric
public import Unfoldings.Geometry.SpatialEnvelopeCutDomain

/-! Entire original finite banks lift to exact metric copies in every larger comparison mesh. -/

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

local instance comparisonFiniteBankIndexFintype : Fintype (T).Index :=
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
local instance comparisonFiniteBankNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonFiniteBankWholeFintype : Fintype W.Index := W.finiteIndex

local notation "MapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S
local notation "OriginalAt[" S "," p "]" =>
  K.compatibleMeshProcessedBankDilation compact nonempty R no_boundary level higher M positive
    inner_disk beta acute W S p


/-- Every original finite current copy stays below the original truncation level. -/
theorem compatibleMeshProcessedWholeMap_height_le (S : (Fcut).parents.ParentFrontier)
    (x : (T).pairedComplex.Realization RetainAt[S]) :
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (MapAt[S] x)).val) ≤ level := by
  have position := K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S x
  have in_clip := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S] x
  rw [M.clip_eq_sublevel, neg_neg] at in_clip
  exact (congrArg (fun z : Space =>
    (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal z)) position).trans_le in_clip


/-- Every point of a whole original finite bank is strictly inside every larger window. -/
theorem compatibleMeshProcessedFiniteBank_positive (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (p : (T).pairedComplex.BoundaryEnd RetainAt[S])
    (u : unitInterval) :
    ∀ j, 0 < SpatialEnvelope.levelEquation M.plane (-later) j
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] (OriginalAt[S,p] u)).val) := by
  have original := K.compatibleMeshProcessedBankDilation_apply compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S p u
  have below := ((congrArg (fun z => (K.clippedExtension slopes compact nonempty).height
    (Cap.horizontal (W.partition.restoreCut CutsAt[S] z).val)) original).trans_le
      (K.compatibleMeshProcessedWholeMap_height_le compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S ((T).pairedComplex.directedBoundaryPath p u))
    ).trans_lt ordered
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith


open Classical in
/-- Construct the whole original finite bank as an exact dilation in the actual larger
comparison mesh. Both original endpoint copies are retained. -/
def compatibleMeshProcessedComparisonFiniteBank (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) :
    unitInterval →ᵈ
      (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  (VAt[later,ordered]).partialPairedMeshCurveLiftDilation ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (0 : ℝ) 1) (convex_Icc _ _) OriginalAt[S,p]
    (K.compatibleMeshProcessedFiniteBank_positive compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered p)

local notation "BankAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p


open Classical in
/-- Every lifted fine-bank point keeps its literal original whole-cut copy. -/
theorem compatibleMeshProcessedComparisonWholeMap_finiteBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (u : unitInterval) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered (BankAt[S,later,ordered,p] u) =
        MapAt[S] ((T).pairedComplex.directedBoundaryPath p u) :=
  ((VAt[later,ordered]).partialPairedMeshMap_curveLift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (0 : ℝ) 1) OriginalAt[S,p]
    (K.compatibleMeshProcessedFiniteBank_positive compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered p) u).trans
    (K.compatibleMeshProcessedBankDilation_apply compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S p u)


open Classical in
/-- Every lifted closed finite bank is embedded with both original endpoints. -/
theorem compatibleMeshProcessedComparisonFiniteBank_isClosedEmbedding
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) :
    Topology.IsClosedEmbedding BankAt[S,later,ordered,p] :=
  Dilation.isClosedEmbedding BankAt[S,later,ordered,p]


open Classical in
/-- Every pairwise distance on the constructed finite bank is its original whole-bank distance. -/
theorem edist_compatibleMeshProcessedComparisonFiniteBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (s t : unitInterval) :
    edist (BankAt[S,later,ordered,p] s) (BankAt[S,later,ordered,p] t) =
      edist (OriginalAt[S,p] s) (OriginalAt[S,p] t) :=
  (VAt[later,ordered]).edist_partialPairedMeshCurveLift_dilation ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]
    (Set.Icc (0 : ℝ) 1) (convex_Icc _ _) OriginalAt[S,p]
    (K.compatibleMeshProcessedFiniteBank_positive compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered p) s t


open Classical in
/-- The entire actual spatial bank trace is unchanged by the larger comparison lift. -/
theorem fold_compatibleMeshProcessedComparisonFiniteBank
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (u : unitInterval) :
    (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      (BankAt[S,later,ordered,p] u) =
        (T).pairedFolding.toSpace RetainAt[S] ((T).pairedComplex.directedBoundaryPath p u) :=
  (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S later ordered _).symm.trans
    ((congrArg (fun z => (W.partition.restoreCut CutsAt[S] z).val)
      (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered p u)).trans
      (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S ((T).pairedComplex.directedBoundaryPath p u)))

end Unfoldings.ConvexRoof
