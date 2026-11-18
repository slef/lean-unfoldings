module

public import Unfoldings.Roof.CompatibleComparisonSubdivision
public import Unfoldings.Roof.NestedCutSubdivision

/-! Actual comparison subdivisions preserve the intermediate original cut metric and fans. -/

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

local instance comparisonCutSubdivisionOldFintype : Fintype (T).Index :=
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
local instance comparisonCutSubdivisionNewFintype (S : (Fcut).parents.ParentFrontier)
    (later : ℝ) (ordered : level < later) : Fintype (NewAt[S,later,ordered]).Index :=
  @Fintype.ofFinite _ (NewAt[S,later,ordered]).finite

open Classical in
/-- The actual old-face subdivision retains exactly the original intermediate cut seam classes. -/
theorem compatibleMeshProcessedComparisonSubdivision_conforming
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :
    (K.compatibleMeshProcessedComparisonSubdivision compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S later ordered).Conforming RetainAt[S]
      ((T).toTriangulation.nestedRetain (NewAt[S,later,ordered]).toTriangulation CutsAt[S]) := by
  apply (T).toTriangulation.nestedSubdivision_conforming
    (NewAt[S,later,ordered]).toTriangulation conforming
    (K.compatibleMeshProcessedComparisonMesh_conforming compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered)
    (K.compatible_section_interior compact nonempty R later (fun v => (higher v).trans ordered) M)
    (K.compatibleMeshProcessedComparisonMesh_faceRefinement compact nonempty R no_boundary level
      higher M positive inner_disk beta acute S later ordered)
    ((inside).mono interior_subset) CutsAt[S]
    (K.isClosed_compatibleMeshProcessedCarrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S) ?_ RetainAt[S]
    (K.compatibleMeshProcessed_removed_edge compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)
    (K.compatibleMeshProcessed_retained_open_edge compact nonempty R no_boundary level higher M
      positive inner_disk beta acute S)
    (K.compatibleMeshProcessedComparisonMesh_cut_aligned compact nonempty R no_boundary level higher
      M positive inner_disk beta acute S later ordered)
  intro f
  exact Disjoint.mono_right
    (K.compatibleMeshProcessedCarrier_subset compact nonempty R no_boundary level higher M positive
      inner_disk beta acute S)
    (K.compatibleMesh_cut_disjoint_interior compact nonempty R no_boundary level higher M positive
      inner_disk f)

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
/-- The whole original intermediate cut is exactly the intrinsic cut of its actual new pieces. -/
def compatibleMeshProcessedComparisonSubdivisionMetricEquiv
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later) :=
  (HAt[S,later,ordered]).metricEquiv

open Classical in
/-- Every original intermediate cut vertex copy has exactly one corresponding fine vertex. -/
theorem existsUnique_compatibleMeshProcessedComparisonSubdivision_vertex
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (coarse : (T).pairedComplex.Vertex RetainAt[S]) :
    ∃! fine : (FineAt[S,later,ordered]).Vertex FineRetainAt[S,later,ordered],
      (HAt[S,later,ordered]).metricEquiv
        ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered] fine) =
          (T).pairedComplex.vertexPoint RetainAt[S] coarse :=
  (HAt[S,later,ordered]).existsUnique_vertex_over
    (K.compatibleMeshProcessedComparisonSubdivision_cornerAnglePreserving compact nonempty R
      no_boundary level higher M positive inner_disk beta acute S later ordered) coarse

open Classical in
/-- Every corresponding actual retained cut-side fan has its exact original total angle. -/
theorem compatibleMeshProcessedComparisonSubdivision_totalAngle_eq
    (S : (Fcut).parents.ParentFrontier) (later : ℝ) (ordered : level < later)
    (fine : (FineAt[S,later,ordered]).Vertex FineRetainAt[S,later,ordered])
    (coarse : (T).pairedComplex.Vertex RetainAt[S])
    (same : (HAt[S,later,ordered]).metricEquiv
      ((FineAt[S,later,ordered]).vertexPoint FineRetainAt[S,later,ordered] fine) =
        (T).pairedComplex.vertexPoint RetainAt[S] coarse) :
    (FineAt[S,later,ordered]).totalAngle FineRetainAt[S,later,ordered] fine =
      (T).pairedComplex.totalAngle RetainAt[S] coarse :=
  (HAt[S,later,ordered]).totalAngle_eq_of_vertexPoint
    (K.compatibleMeshProcessedComparisonSubdivision_cornerAnglePreserving compact nonempty R
      no_boundary level higher M positive inner_disk beta acute S later ordered) fine coarse same

end Unfoldings.ConvexRoof
