module

public import Unfoldings.Roof.CompatibleComparisonChainRefinement
public import Unfoldings.Roof.SpatialEnvelopeInteriorBanks
public import Unfoldings.Roof.CompletionChainLength
public import Unfoldings.Roof.CompletionOriginalSpatial

/-! Actual comparison chains retain their whole-cut geometry under physical cap completion. -/

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

local instance comparisonPhysicalCompletionIndexFintype : Fintype (T).Index :=
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
local instance comparisonPhysicalCompletionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

variable (W : R.WholeCutModel M)

local instance comparisonPhysicalCompletionWholeFintype : Fintype W.Index := W.finiteIndex

local notation "NewRoofAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
  ConformingAt[S,L,h]
  (K.compatible_section_interior compact nonempty R L HigherAt[L,h] M)
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

variable {φ : ℝ} {region : Set Plane}

open Classical in
local instance comparisonPhysicalCompletionFineFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations) : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The physical original-face part of a comparison cap maps to the same original
whole cut, retaining actual metric copies rather than spatial coincidence. -/
@[macro_inline] def compatibleMeshProcessedComparisonCompletedWholeMap
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations)
    (y : E.originalComplex.Realization (E.originalRetain NewRetainAt[S,later,ordered])) :
    W.partition.Cut CutsAt[S] :=
  NewMapAt[S,later,ordered] (E.originalMetricEquiv NewRetainAt[S,later,ordered] y)

open Classical in
/-- Physical completion keeps the entire original spatial folding of every cut-side copy. -/
theorem restore_compatibleMeshProcessedComparisonCompletedWholeMap
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations)
    (y : E.originalComplex.Realization (E.originalRetain NewRetainAt[S,later,ordered])) :
    (W.partition.restoreCut CutsAt[S]
      (K.compatibleMeshProcessedComparisonCompletedWholeMap compact nonempty R no_boundary level
        higher M positive inner_disk beta acute W S later ordered E y)).val =
      (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
        (E.originalRetain NewRetainAt[S,later,ordered]) y :=
  (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher
    M positive inner_disk beta acute W S later ordered
    (E.originalMetricEquiv NewRetainAt[S,later,ordered] y)).trans
      (E.originalMetricEquiv_toSpace NewRetainAt[S,later,ordered] y).symm

open Classical in
/-- Construct the complete physical refinement of an actual comparison chain.
Strict starting heights derive all original cut labels; no fine-fan or angle
matching certificate is supplied. -/
def compatibleMeshProcessedComparisonPhysicalRefinement
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations) {n : ℕ}
    (coarse : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (below : ∀ j, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        (coarse.point j))) < later) :
    E.OriginalChainRefinement NewRetainAt[S,later,ordered] coarse := by
  apply E.originalChainRefinement
  intro j
  apply (NewAt[S,later,ordered]).toTriangulation.boundaryEnd_is_cut_of_strict_height
    ConformingAt[S,later,ordered]
    (K.compatible_section_interior compact nonempty R later HigherAt[later,ordered] M)
  have height_bound := below j
  rw [M.height_eq]
  linarith

open Classical in
/-- Physical refinement retains every original whole-cut bank point, including
its actual endpoint and subdivision copies. -/
theorem compatibleMeshProcessedComparisonPhysicalRefinement_whole_trace
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (E : (NewRoofAt[S,later,ordered]).CompletionMesh φ region
      (NewRoofAt[S,later,ordered]).originalEdgeEquations) {n : ℕ}
    (coarse : ((NewAt[S,later,ordered]).pairedComplex.boundarySystem
      NewRetainAt[S,later,ordered]).Chain n)
    (below : ∀ j, (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((NewAt[S,later,ordered]).pairedFolding.boundaryPosition
        (coarse.point j))) < later) :
    let refined := K.compatibleMeshProcessedComparisonPhysicalRefinement compact nonempty R
      no_boundary level higher M positive inner_disk beta acute S later ordered E coarse below
    (K.compatibleMeshProcessedComparisonCompletedWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered E) ''
        E.originalComplex.boundaryChainTrace refined.chain =
      NewMapAt[S,later,ordered] ''
        (NewAt[S,later,ordered]).pairedComplex.boundaryChainTrace coarse :=
  (K.compatibleMeshProcessedComparisonPhysicalRefinement compact nonempty R no_boundary level
    higher M positive inner_disk beta acute S later ordered E coarse below).observed_trace_image
    NewMapAt[S,later,ordered]

end Unfoldings.ConvexRoof
