module

public import Unfoldings.Roof.CompatibleComparisonCutSubdivision
public import Unfoldings.Roof.NestedInteriorFans

/-! Original interior cut-side vertices keep their exact angles in larger comparison meshes. -/

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

local instance comparisonOriginalFanOldFintype : Fintype (T).Index :=
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
local instance comparisonOriginalFanNewFintype (S : (Fcut).parents.ParentFrontier)
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

open Classical in
/-- The unique original cut-side vertex in the complete physical old-face subdivision. -/
def compatibleMeshProcessedComparisonSubdivisionVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    (FineAt[S,later,ordered]).Vertex FineRetainAt[S,later,ordered] :=
  (K.existsUnique_compatibleMeshProcessedComparisonSubdivision_vertex compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S later ordered coarse).choose

open Classical in
theorem compatibleMeshProcessedComparisonSubdivisionVertex_eq
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    (HAt[S,later,ordered]).metricEquiv
      ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered]
        (K.compatibleMeshProcessedComparisonSubdivisionVertex compact nonempty R no_boundary level
          higher M positive inner_disk beta acute S later ordered coarse)) =
        (T).pairedComplex.vertexPoint RetainAt[S] coarse :=
  (K.existsUnique_compatibleMeshProcessedComparisonSubdivision_vertex compact nonempty R no_boundary
    level higher M positive inner_disk beta acute S later ordered coarse).choose_spec.1

local notation "VertexAt[" S "," L "," h "," c "]" =>
  K.compatibleMeshProcessedComparisonSubdivisionVertex compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h c

open Classical in
/-- The corresponding actual original vertex in the whole larger cut mesh. -/
def compatibleMeshProcessedComparisonOriginalVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    (NewAt[S,later,ordered]).pairedComplex.Vertex
      ((NewAt[S,later,ordered]).toTriangulation.retainOutside CutsAt[S]) :=
  (NewAt[S,later,ordered]).pairedComplex.includeRestrictedVertex
    ((T).toTriangulation.nestedPieceSet (NewAt[S,later,ordered]).toTriangulation)
    ((NewAt[S,later,ordered]).toTriangulation.retainOutside CutsAt[S])
    VertexAt[S,later,ordered,coarse]

open Classical in
/-- Literal original spatial coordinates survive the exact cut-side vertex correspondence. -/
theorem fold_compatibleMeshProcessedComparisonSubdivisionVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    ((T).toTriangulation.nestedFolding (NewAt[S,later,ordered]).toTriangulation).toSpace
      FineRetainAt[S,later,ordered]
      ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered]
        VertexAt[S,later,ordered,coarse]) =
      (T).pairedFolding.toSpace RetainAt[S] ((T).pairedComplex.vertexPoint RetainAt[S] coarse) := by
  have folded := (T).toTriangulation.nestedSubdivision_fold_metricEquiv
    (NewAt[S,later,ordered]).toTriangulation
    (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered)
    RetainAt[S] FineRetainAt[S,later,ordered] HAt[S,later,ordered]
    ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered]
      VertexAt[S,later,ordered,coarse])
  exact folded.symm.trans (congrArg ((T).pairedFolding.toSpace RetainAt[S])
    (K.compatibleMeshProcessedComparisonSubdivisionVertex_eq compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered coarse))

local notation "NewRetainAt[" S "," L "," h "]" => SpatialEnvelope.Triangulation.retainOutside
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation NewAt[S,L,h]) CutsAt[S]
local notation "OriginalVertexAt[" S "," L "," h "," c "]" =>
  K.compatibleMeshProcessedComparisonOriginalVertex compact nonempty R no_boundary level higher M
    positive inner_disk beta acute S L h c

open Classical in
/-- The full comparison mesh retains the literal original spatial vertex. -/
theorem fold_compatibleMeshProcessedComparisonOriginalVertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    (NewAt[S,later,ordered]).pairedFolding.toSpace NewRetainAt[S,later,ordered]
      ((NewAt[S,later,ordered]).pairedComplex.vertexPoint NewRetainAt[S,later,ordered]
        OriginalVertexAt[S,later,ordered,coarse]) =
      (T).pairedFolding.toSpace RetainAt[S] ((T).pairedComplex.vertexPoint RetainAt[S] coarse) :=
  ((NewAt[S,later,ordered]).pairedFolding.toSpace_includeRestrictedVertex
    ((T).toTriangulation.nestedPieceSet (NewAt[S,later,ordered]).toTriangulation)
    NewRetainAt[S,later,ordered] VertexAt[S,later,ordered,coarse]).trans
      (K.fold_compatibleMeshProcessedComparisonSubdivisionVertex compact nonempty R no_boundary
        level higher M positive inner_disk beta acute S later ordered coarse)

open Classical in
/-- Every original cut-side vertex below the old rim keeps its exact fan in the full larger mesh. -/
theorem compatibleMeshProcessedComparisonOriginalVertex_totalAngle_eq
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S])
    (below : (K.clippedExtension slopes compact nonempty).height
      (Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
        ((T).pairedComplex.vertexPoint RetainAt[S] coarse))) < level) :
    (NewAt[S,later,ordered]).pairedComplex.totalAngle NewRetainAt[S,later,ordered]
      OriginalVertexAt[S,later,ordered,coarse] =
        (T).pairedComplex.totalAngle RetainAt[S] coarse := by
  have original_inside : Cap.horizontal ((T).pairedFolding.toSpace RetainAt[S]
      ((T).pairedComplex.vertexPoint RetainAt[S] coarse)) ∈
        interior (SpatialEnvelope.clip M.plane (-level)) := by
    rw [M.clip_eq_sublevel, neg_neg]
    exact (K.clippedExtension slopes compact nonempty).mem_interior_sublevel below
  have fine_inside := Eq.mpr (congrArg
    (fun z : Space => Cap.horizontal z ∈ interior (SpatialEnvelope.clip M.plane (-level)))
    (K.fold_compatibleMeshProcessedComparisonSubdivisionVertex compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered coarse)) original_inside
  exact ((T).toTriangulation.nested_interior_totalAngle
    (NewAt[S,later,ordered]).toTriangulation
    (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered) CutsAt[S]
    VertexAt[S,later,ordered,coarse] fine_inside).trans
      (K.compatibleMeshProcessedComparisonSubdivision_totalAngle_eq compact nonempty R no_boundary
        level higher M positive inner_disk beta acute S later ordered
        VertexAt[S,later,ordered,coarse] coarse
        (K.compatibleMeshProcessedComparisonSubdivisionVertex_eq compact nonempty R no_boundary
          level higher M positive inner_disk beta acute S later ordered coarse))

end Unfoldings.ConvexRoof
