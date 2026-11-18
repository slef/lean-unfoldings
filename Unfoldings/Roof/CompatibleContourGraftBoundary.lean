module

public import Unfoldings.Roof.CompatibleContourGraftCells
public import Unfoldings.Roof.CompatibleContourMarkCarrier
public import Unfoldings.Metric.BankStackCellBoundary
public import Unfoldings.Metric.BoundaryCellInteriorChart
public import Unfoldings.Metric.BallChartTransport

/-! Every primitive seam of the complete actual graft lies on original planar-cell boundaries. -/

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

local instance contourGraftBoundaryMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e

variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourGraftBoundaryWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourCells compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourCellInner compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourCellCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- The complete actual graft introduces no interior planar-cell attachments.
All roof and gap bank-boundary placements are derived from the original geometric cuts. -/
theorem compatibleContourCellGlue_boundary :
    ∀ (ij : Σ i, Index i) (p : Cells ij.1 ij.2),
      p ∈ MetricGluing.seamSupport (MetricGluing.NestedCell (fun i j => Cells i j))
        (K.compatibleContourCellGlue compact nonempty R no_boundary level higher M positive
          inner_disk beta acute contour starts W models) ij →
        p.val ∉ interior (Cells ij.1 ij.2) := by
  apply MetricGluing.bankStackCells_boundary Cells Inner Coordinates Stack Base Gap
  · exact K.compatibleContourCellInner_boundary compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models
  · intro bank side t ij p named
    apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
    intro j q equal
    cases bank with
    | inl vertex =>
      exact W.cell_boundary_of_restore_mem j q _ equal
        (K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W vertex.val vertex.property side t)
    | inr edge =>
      exact W.cell_boundary_of_restore_mem j q _ equal
        (K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W edge side t)
  · intro bank event member side t ij p named
    apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
    intro j q equal
    cases bank with
    | inl vertex =>
      exact (models event).planarCell_edge_boundary side _ t j q equal
    | inr edge =>
      exact (models event).planarCell_tail_boundary side t j q equal

/-- Every actual roof or gap cell interior already has a whole planar metric ball in the graft.
The remaining local regularity argument is confined to the actual seam and vertex classes. -/
theorem compatibleContourGraft_cell_interior_chart (ij : Σ i, Index i) (p : Cells ij.1 ij.2)
    (interior_point : p.val ∈ interior (Cells ij.1 ij.2)) :
    HasMetricBallChart Plane
      (K.compatibleContourGraftCellIsometry compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models
        (MetricGluing.of (MetricGluing.NestedCell (fun i j => Cells i j))
          (K.compatibleContourCellGlue compact nonempty R no_boundary level higher M positive
            inner_disk beta acute contour starts W models) ij p)) :=
  (MetricGluing.hasMetricBallChart_of_cell_interior
    (fun ij : Σ i, Index i => Cells ij.1 ij.2)
    (K.compatibleContourCellGlue compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (K.compatibleContourCellGlue_boundary compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models) ij p interior_point).isometryEquiv
    (K.compatibleContourGraftCellIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)

end Unfoldings.ConvexRoof
