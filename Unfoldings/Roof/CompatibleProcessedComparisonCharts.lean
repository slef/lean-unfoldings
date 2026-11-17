module

public import Unfoldings.Roof.CompatibleProcessedComparisonMesh
public import Unfoldings.Roof.CompatiblePartialWindowPairedCenters

/-! Actual larger comparison meshes preserve original whole-cut copies and local metric balls. -/

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

local instance processedComparisonChartIndexFintype : Fintype (T).Index :=
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
local instance processedComparisonChartNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance processedComparisonChartWholeFintype : Fintype W.Index := W.finiteIndex

open Classical in
/-- Include the larger actual finite comparison mesh in the same original intermediate cut. -/
@[macro_inline] def compatibleMeshProcessedComparisonWholeMap
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (y : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered]) :
    W.partition.Cut CutsAt[S] :=
  (VAt[later,ordered]).partialPairedMeshMap ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] y

open Classical in
/-- Every original whole-cut copy strictly below the new level has an exact whole-ball chart
in the constructed larger comparison mesh. All geometric seam conditions are derived. -/
theorem exists_compatibleMeshProcessedComparison_ball_chart
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (x : W.partition.Cut CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < later) :
    ∃ source : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered],
      K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ chart : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (chart z).val =
          K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
            positive inner_disk beta acute W S later ordered z.val := by
  apply (VAt[later,ordered]).exists_partialPairedMesh_ball_chart ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] x
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

open Classical in
/-- The same inclusion keeps the original spatial point at every fine bank or corner copy. -/
theorem restore_compatibleMeshProcessedComparisonWholeMap
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (y : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered]) :
    (W.partition.restoreCut CutsAt[S]
      (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered y)).val =
      (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered] y :=
  (VAt[later,ordered]).restore_partialPairedMeshMap ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] y

open Classical in
/-- Larger comparison inclusions are nonexpanding in the actual original whole-cut metric. -/
theorem compatibleMeshProcessedComparisonWholeMap_lipschitz
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :
    LipschitzWith 1 (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered) :=
  (VAt[later,ordered]).partialPairedMeshMap_lipschitz ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered]

open Classical in
/-- The uniquely determined actual fine copy of an original point in the larger window. -/
def compatibleMeshProcessedComparisonLift (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) (x : W.partition.Cut CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < later) :
    (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered] :=
  (VAt[later,ordered]).partialPairedMeshLift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] x
    (by
      apply SpatialEnvelope.levelEquation_positive
      rw [M.height_eq]
      linarith)

open Classical in
/-- Lifting to the larger comparison mesh retains the literal original whole-cut copy. -/
@[simp] theorem compatibleMeshProcessedComparisonWholeMap_lift
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (x : W.partition.Cut CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < later) :
    K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered
      (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
        positive inner_disk beta acute W S later ordered x below) = x :=
  (VAt[later,ordered]).partialPairedMeshMap_lift ProperAt[later,ordered] FullAt[later,ordered]
    (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S] ClosedAt[S]
    IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] x _

end Unfoldings.ConvexRoof
