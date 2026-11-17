module

public import Unfoldings.Roof.CompatibleProcessedComparisonCharts
public import Unfoldings.Metric.PlacedBallComposition

/-! Original physically placed model charts in larger intermediate-cut comparison meshes. -/

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

local instance comparisonPlacedChartIndexFintype : Fintype (T).Index :=
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
local instance comparisonPlacedChartNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonPlacedChartWholeFintype : Fintype W.Index := W.finiteIndex

open Classical in
/-- A specified larger-mesh copy has its own whole original-cut neighborhood. -/
theorem compatibleMeshProcessedComparison_ball_chart_at
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (y : (NewAt[S,later,ordered]).pairedComplex.Realization NewRetainAt[S,later,ordered])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] y)) < later) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ B : Metric.eball y (ENNReal.ofReal radius) ≃ᵢ
      Metric.eball
        (K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W S later ordered y) (ENNReal.ofReal radius),
      ∀ z, (B z).val = K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary
        level higher M positive inner_disk beta acute W S later ordered z.val := by
  apply (VAt[later,ordered]).partialPairedMesh_ball_chart_at ProperAt[later,ordered]
    FullAt[later,ordered] (NewAt[S,later,ordered]).toTriangulation DomainAt[later] Heights CutsAt[S]
    ClosedAt[S] IncludedAt[S] OutsideAt[S,later,ordered] W ConformingAt[S,later,ordered]
    NewRetainAt[S,later,ordered] RemovedAt[S,later,ordered] RetainedAt[S,later,ordered] y
  apply SpatialEnvelope.levelEquation_positive
  rw [M.height_eq]
  linarith

open Classical in
/-- A physically placed whole-cut model pulls back to the canonical larger-mesh copy,
with exactly its original center and supporting frame. All inclusion geometry is constructed. -/
theorem exists_compatibleMeshProcessedComparison_placed_chart
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (x : W.partition.Cut CutsAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal (W.partition.restoreCut CutsAt[S] x).val) < later)
    {Z : Type*} [MetricSpace Z] (place : Z → Space) (injective : Function.Injective place)
    (a : Z) (model_place : place a = (W.partition.restoreCut CutsAt[S] x).val)
    (model_chart : ∃ radius : ℝ, 0 < radius ∧
      ∃ H : Metric.eball x (ENNReal.ofReal radius) ≃ᵢ Metric.ball a radius,
        ∀ z, place (H z).val = (W.partition.restoreCut CutsAt[S] z.val).val) :
    ∃ radius : ℝ, ∃ radius_positive : 0 < radius, ∃ D : Metric.eball
        (K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level higher M
          positive inner_disk beta acute W S later ordered x below) (ENNReal.ofReal radius) ≃ᵢ
        Metric.ball a radius,
      (D ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_positive)⟩).val = a ∧
      ∀ z, place (D z).val = (NewAt[S,later,ordered]).pairedFolding.toSpace
        NewRetainAt[S,later,ordered] z.val := by
  let source := K.compatibleMeshProcessedComparisonLift compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S later ordered x below
  let inclusion := K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W S later ordered
  have image : inclusion source = x :=
    K.compatibleMeshProcessedComparisonWholeMap_lift compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered x below
  have source_fold : (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      source = (W.partition.restoreCut CutsAt[S] x).val :=
    (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered source).symm.trans
        (congrArg (fun p => (W.partition.restoreCut CutsAt[S] p).val) image)
  have source_below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
        source)) < later :=
    (congrArg (fun p => (K.clippedExtension slopes compact nonempty).height (Cap.horizontal p))
      source_fold).trans_lt below
  obtain ⟨ρ, ρpos, B, agrees_B⟩ :=
    K.compatibleMeshProcessedComparison_ball_chart_at compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S later ordered source source_below
  obtain ⟨σ, σpos, H, agrees_H⟩ := model_chart
  obtain ⟨radius, radius_positive, D, agrees⟩ := exists_composed_placed_ball_chart inclusion
    ((NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered])
    (fun p => (W.partition.restoreCut CutsAt[S] p).val) place injective image
    (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered) ρpos σpos B agrees_B H agrees_H
      model_place
  have center : (D ⟨source,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr radius_positive)⟩).val = a :=
    injective ((agrees _).trans (source_fold.trans model_place.symm))
  exact ⟨radius, radius_positive, D, center, agrees⟩

end Unfoldings.ConvexRoof
