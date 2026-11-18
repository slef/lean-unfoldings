module

public import Unfoldings.Roof.CompatibleComparisonOriginalFans
public import Unfoldings.Roof.CompatibleProcessedComparisonCharts
public import Unfoldings.Roof.CompatibleProcessedMeshCharts
public import Unfoldings.Geometry.SpatialEnvelopeCutLiftUnique
public import Unfoldings.Complex.FaceRestrictionMap

/-! Larger-mesh subdivision maps retain the literal original whole-cut metric copies. -/

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

local instance comparisonSubdivisionMapOldFintype : Fintype (T).Index :=
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
local instance comparisonSubdivisionMapNewFintype (S : (Fcut).parents.ParentFrontier)
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

local instance comparisonSubdivisionMapWholeFintype : Fintype W.Index := W.finiteIndex

local notation "OldMapAt[" S "]" => K.compatibleMeshProcessedWholeMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute W S
local notation "NewMapAt[" S "," L "," h "]" =>
  K.compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W S L h

open Classical in
/-- Subdivision and original whole-cut maps retain exactly the same bank copies. -/
theorem compatibleMeshProcessedComparisonWholeMap_subdivision
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (x : (FineAt[S,later,ordered]).Realization FineRetainAt[S,later,ordered]) :
    NewMapAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.includeRestricted PiecesAt[S,later,ordered]
        NewRetainAt[S,later,ordered] x) = OldMapAt[S] ((HAt[S,later,ordered]).metricEquiv x) := by
  apply congrFun (W.partition.continuous_cut_lifts_eq
    ((T).toTriangulation.nestedFolding (NewAt[S,later,ordered]).toTriangulation)
    FineRetainAt[S,later,ordered] CutsAt[S]
    (fun x => NewMapAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.includeRestricted PiecesAt[S,later,ordered]
        NewRetainAt[S,later,ordered] x))
    (fun x => OldMapAt[S] ((HAt[S,later,ordered]).metricEquiv x)) ?_ ?_ ?_ ?_ ?_) x
  · exact (K.compatibleMeshProcessedComparisonWholeMap_lipschitz compact nonempty R no_boundary
      level higher M positive inner_disk beta acute W S later ordered).continuous.comp
        ((NewAt[S,later,ordered]).pairedComplex.includeRestricted_lipschitz
          PiecesAt[S,later,ordered] NewRetainAt[S,later,ordered]).continuous
  · exact (K.compatibleMeshProcessedWholeMap_lipschitz compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S).continuous.comp
        (HAt[S,later,ordered]).metricEquiv.continuous
  · intro x
    exact (K.restore_compatibleMeshProcessedComparisonWholeMap compact nonempty R no_boundary level
      higher M positive inner_disk beta acute W S later ordered _).trans
        ((NewAt[S,later,ordered]).pairedFolding.toSpace_includeRestricted PiecesAt[S,later,ordered]
          NewRetainAt[S,later,ordered] x)
  · intro x
    exact (K.restore_compatibleMeshProcessedWholeMap compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W S _).trans
        ((T).toTriangulation.nestedSubdivision_fold_metricEquiv
          (NewAt[S,later,ordered]).toTriangulation
          (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary
            level higher M positive inner_disk beta acute S later ordered)
          RetainAt[S] FineRetainAt[S,later,ordered] HAt[S,later,ordered] x)
  · intro i
    exact (NewAt[S,later,ordered]).toTriangulation.physical_cut_disjoint_face_interior CutsAt[S]
      (K.compatibleMeshProcessedComparisonMesh_cut_disjoint_interior compact nonempty R no_boundary
        level higher M positive inner_disk beta acute S later ordered) i.val

open Classical in
/-- Corresponding full-mesh vertices represent the exact original whole-cut vertex copy. -/
theorem compatibleMeshProcessedComparisonWholeMap_originalVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    NewMapAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        (K.compatibleMeshProcessedComparisonOriginalVertex compact nonempty R no_boundary level
          higher M positive inner_disk beta acute S later ordered coarse)) =
      OldMapAt[S] ((T).pairedComplex.vertexPoint RetainAt[S] coarse) := by
  let fine := K.compatibleMeshProcessedComparisonSubdivisionVertex compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S later ordered coarse
  have included := (NewAt[S,later,ordered]).pairedComplex.includeRestricted_vertexPoint
    PiecesAt[S,later,ordered] NewRetainAt[S,later,ordered] fine
  have same := K.compatibleMeshProcessedComparisonWholeMap_subdivision compact nonempty R
    no_boundary level higher M positive inner_disk beta acute W S later ordered
    ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered] fine)
  exact (congrArg NewMapAt[S,later,ordered] included).symm.trans
    (same.trans (congrArg OldMapAt[S]
      (K.compatibleMeshProcessedComparisonSubdivisionVertex_eq compact nonempty R no_boundary level
        higher M positive inner_disk beta acute S later ordered coarse)))

end Unfoldings.ConvexRoof
