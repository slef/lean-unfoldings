module

public import Unfoldings.Roof.CompatibleContourGapModels
public import Unfoldings.Roof.CompatibleMeshWindowCharts
public import Unfoldings.Complex.ContourSourceBankSides
public import Unfoldings.Polyhedron.ContourParentBankMetric
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Metric.BankStackGraft

/-! Assemble the actual roof and positive contour gaps along their closed finite parent banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

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

local instance compatibleContourFiniteGraftIndexFintype : Fintype (T).Index :=
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

local instance compatibleContourFiniteGraftWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

/-- Each original finite parent-bank mark is its actual whole-cut metric copy. -/
def compatibleContourParentMark (vertex : (T).pairedComplex.Vertex Set.univ)
    (nonroot : vertex ∉ (Fcut).parents.roots) (side : Bool) (t : unitInterval) : W.Cut :=
  Map ((T).pairedComplex.directedBoundaryPath
    ((T).pairedComplex.contourParentBank (Fcut).selection contour (Fcut).boundary_roots starts
      vertex nonroot side) t)

/-- Inclusion retains all intrinsic distances of each entire original finite bank. -/
theorem compatibleWholeMap_edist_bank (p : (T).pairedComplex.BoundaryEnd (Fcut).retain)
    (s t : unitInterval) :
    edist (Map ((T).pairedComplex.directedBoundaryPath p s))
      (Map ((T).pairedComplex.directedBoundaryPath p t)) =
      edist ((T).pairedComplex.directedBoundaryPath p s)
        ((T).pairedComplex.directedBoundaryPath p t) := by
  apply le_antisymm
  · exact (K.compatibleMeshWholeMap_lipschitz compact nonempty R no_boundary level higher M
      positive inner_disk beta acute W _ _).trans_eq (one_mul _)
  · rw [(T).pairedFolding.edist_directedBoundaryPath_eq_spatial]
    have lower := (PolygonalPoint.ambient_lipschitz.comp
      (W.partition.restoreCut_lipschitz R.carrier))
      (Map ((T).pairedComplex.directedBoundaryPath p s))
      (Map ((T).pairedComplex.directedBoundaryPath p t))
    simpa only [Function.comp_apply, ENNReal.coe_one, one_mul,
      K.restore_compatibleMeshWholeMap] using lower

/-- The two actual closed parent-bank copies retain identical edge metrics. -/
theorem edist_compatibleContourParentMark_sides (vertex : (T).pairedComplex.Vertex Set.univ)
    (nonroot : vertex ∉ (Fcut).parents.roots) (s t : unitInterval) :
    edist (K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex nonroot false s)
      (K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex nonroot false t) =
    edist (K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex nonroot true s)
      (K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex nonroot true t) := by
  let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
    (Fcut).boundary_roots starts vertex nonroot
  have first := K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W (bank false) s t
  have last := K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M
    positive inner_disk beta acute W (bank true) s t
  exact first.trans (((T).pairedFolding.edist_contourParentBank_sides (Fcut).selection contour
    (Fcut).boundary_roots starts vertex nonroot s t).trans last.symm)

/-- The original roof and every actual positive source gap are retained as metric pieces. -/
def compatibleContourGraftPiece :
    Option ((T).pairedComplex.PositiveContourSource (Fcut).selection contour) → Type
  | none => W.Cut
  | some event => PolygonalPoint (models event).region

instance compatibleContourGraftPieceEMetricSpace (i) : EMetricSpace
    (K.compatibleContourGraftPiece compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models i) := by
  cases i <;> dsimp only [compatibleContourGraftPiece] <;> infer_instance

/-- On every affected original edge, use its exact index in the corresponding complete gap. -/
def compatibleContourGapEdgeMark (vertex : (T).pairedComplex.Vertex Set.univ)
    (nonroot : vertex ∉ (Fcut).parents.roots)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex)
    (side : Bool) (t : unitInterval) : PolygonalPoint (models event).region :=
  (models event).edgePoint side
    ((T).pairedComplex.contourGapBankIndex (Fcut).selection contour vertex nonroot event
      ((T).pairedComplex.mem_contourEdgeGapStack (Fcut).selection contour vertex event |>.mpr
        ((T).pairedComplex.mem_contourSavedGapStack (Fcut).selection contour vertex event |>.mp
          member))) t

/-- This is the genuine route-metric graft along all finite original parent edges.
Whole terminal-tail attachments are a separate further gluing operation. -/
abbrev compatibleContourFiniteGraft :=
  MetricGluing.BankStackGraft
    (K.compatibleContourGraftPiece compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (fun vertex : {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots} =>
      (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex.val)
    (fun vertex => K.compatibleContourParentMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W vertex.val vertex.property)
    (fun vertex => K.compatibleContourGapEdgeMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models vertex.val vertex.property)

end Unfoldings.ConvexRoof
