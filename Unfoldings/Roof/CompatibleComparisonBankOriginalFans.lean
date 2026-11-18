module

public import Unfoldings.Roof.CompatibleComparisonSubdivisionMap
public import Unfoldings.Roof.CompatibleComparisonFiniteBanks
public import Unfoldings.Roof.CompatibleProcessedComparisonFiber

/-! Actual lifted finite banks retain original full-mesh cut vertices and one-sided angles. -/

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

local instance comparisonBankOriginalOldFintype : Fintype (T).Index :=
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

open Classical in
local instance comparisonBankOriginalNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

local notation "HAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonSubdivision_conforming compact nonempty R no_boundary level
    higher M positive inner_disk beta acute S L h
local notation "FineAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.nestedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])
local notation "FineRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.nestedRetain
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]

local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "PiecesAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.nestedPieceSet
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h])

variable (W : R.WholeCutModel M)

local instance comparisonBankOriginalWholeFintype : Fintype W.Index := W.finiteIndex

local notation "OldMapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

local notation "LiftAt[" S "," L "," h "," p "]" =>
  K.compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h p
local notation "OriginalVertexAt[" S "," L "," h "," c "]" =>
  K.compatibleMeshProcessedComparisonOriginalVertex compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h c

open Classical in
/-- A lifted old bank meeting an original vertex keeps that exact original cut-side copy. -/
theorem compatibleMeshProcessedComparisonFiniteBank_eq_originalVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (u : unitInterval)
    (coarse : (T).pairedComplex.Vertex RetainAt[S])
    (at_vertex : (T).pairedComplex.directedBoundaryPath p u =
      (T).pairedComplex.vertexPoint RetainAt[S] coarse) :
    LiftAt[S,later,ordered,p] u =
      (NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        OriginalVertexAt[S,later,ordered,coarse] := by
  refine K.compatibleMeshProcessedComparisonWholeMap_injective_at compact nonempty R no_boundary
    level higher M positive inner_disk beta acute W S later ordered
    (LiftAt[S,later,ordered,p] u) ?_ _ ?_
  · have original_height := (T).toTriangulation.fold_horizontal_mem_clip RetainAt[S]
      ((T).pairedComplex.directedBoundaryPath p u)
    rw [M.clip_eq_sublevel, neg_neg] at original_height
    have folded := K.fold_compatibleMeshProcessedComparisonFiniteBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered p u
    exact ((congrArg (fun z : Space => (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal z)) folded).trans_le original_height).trans_lt ordered
  · exact (K.compatibleMeshProcessedComparisonWholeMap_finiteBank compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered p u).trans
        ((congrArg OldMapAt[S] at_vertex).trans
          (K.compatibleMeshProcessedComparisonWholeMap_originalVertex compact nonempty R no_boundary
            level higher M positive inner_disk beta acute W S later ordered coarse).symm)

open Classical in
/-- An actual lifted-bank vertex at an old corner has its exact original one-sided fan angle. -/
theorem compatibleMeshProcessedComparisonFiniteBank_original_totalAngle
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (p : (T).pairedComplex.BoundaryEnd RetainAt[S]) (u : unitInterval)
    (coarse : (T).pairedComplex.Vertex RetainAt[S])
    (fine : (NewAt[S,later,ordered]).pairedComplex.Vertex NewRetainAt[S,later,ordered])
    (at_vertex : (T).pairedComplex.directedBoundaryPath p u =
      (T).pairedComplex.vertexPoint RetainAt[S] coarse)
    (matched : (NewAt[S,later,ordered]).pairedComplex.vertexPoint
      NewRetainAt[S,later,ordered] fine = LiftAt[S,later,ordered,p] u)
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.vertexPoint RetainAt[S] coarse))) < level) :
    (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered] fine =
      (T).pairedComplex.totalAngle RetainAt[S] coarse := by
  have same := (NewAt[S,later,ordered]).pairedComplex.vertexPoint_injective
    NewRetainAt[S,later,ordered] (matched.trans
      (K.compatibleMeshProcessedComparisonFiniteBank_eq_originalVertex compact nonempty R
        no_boundary level higher M positive inner_disk beta acute W S later ordered p u coarse at_vertex))
  exact (congrArg ((NewAt[S,later,ordered]).pairedComplex.totalAngle
    NewRetainAt[S,later,ordered]) same).trans
      (K.compatibleMeshProcessedComparisonOriginalVertex_totalAngle_eq compact nonempty R
        no_boundary level higher M positive inner_disk beta acute S later ordered coarse below)

end Unfoldings.ConvexRoof
