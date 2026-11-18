module

public import Unfoldings.Roof.CompatibleContourGraft
public import Unfoldings.Geometry.BankGapClosedEmbeddings

/-! Actual original roof and gap bank marks have closed intrinsic images at every attachment. -/

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

local instance contourBankEmbeddingMeshFintype : Fintype (T).Index :=
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

local instance contourBankEmbeddingWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

local notation "RootAt[" e "]" => K.compatibleMeshTerminalRoot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute (Subtype.val e)
  (TriangleComplex.contourTerminalEdge_positive D Selection e)
local notation "EndAt[" e "," side "]" =>
  K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive inner_disk
    beta acute contour starts W (Subtype.val e) (And.left (Subtype.property e)) side 1

/-- Every actual closed parent bank has its exact original positive length ratio. -/
def compatibleContourParentDilation (vertex : (T).pairedComplex.Vertex Set.univ)
    (nonroot : vertex ∉ (Fcut).parents.roots) (side : Bool) : unitInterval →ᵈ W.Cut where
  toFun := K.compatibleContourParentMark compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W vertex nonroot side
  edist_eq' := by
    let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
      (Fcut).boundary_roots starts vertex nonroot side
    refine ⟨Real.toNNReal ((T).pairedComplex.boundaryBankLength bank),
      (Real.toNNReal_pos.mpr ((T).pairedComplex.boundaryBankLength_pos bank)).ne', ?_⟩
    intro s t
    exact (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level higher M positive
      inner_disk beta acute W bank s t).trans
      ((T).pairedFolding.edist_directedBoundaryPath_eq_length bank s t)

/-- Every actual whole terminal bank has the same positive ratio as its last finite edge. -/
def compatibleContourTailDilation
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) :
    ℝ≥0 →ᵈ W.Cut where
  toFun := K.compatibleContourTerminalMark compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W edge side
  edist_eq' := by
    let bank := (T).pairedComplex.contourParentBank (Fcut).selection contour
      (Fcut).boundary_roots starts edge.val edge.property.1 false
    refine ⟨Real.toNNReal ((T).pairedComplex.boundaryBankLength bank),
      (Real.toNNReal_pos.mpr ((T).pairedComplex.boundaryBankLength_pos bank)).ne', ?_⟩
    exact K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side

/-- Both actual canonical gap banks have genuine finite edges, with no supplied nonzero data. -/
theorem compatibleContourGapBank_edge_ne_zero
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (side : Bool) (k : Fin (LengthAt[contour,event] + 1)) :
    ((models event).bank side).chain.edge k ≠ 0 := by
  have first := (T).pairedComplex.boundaryChainRoll_edge_ne_zero
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],
      SpanAt[contour,event]] k
  cases side
  · exact first
  · change ((BankAt[contour,starts,event]).openings
      (PolygonalChain.castOpenings SpanAt[contour,event]
        ((T).pairedComplex.contourRootwardOpenings (Fcut).selection contour event.val.succ
          VertexAt[contour,event]))).chain.edge k ≠ 0
    rw [PolygonalRay.openings_chain, PolygonalChain.openings_edge]
    exact mul_ne_zero (polarRay_ne_zero _) first

/-- Both actual infinite gap directions are genuine, including one-edge source gaps. -/
theorem compatibleContourGapBank_direction_ne_zero
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour) (side : Bool) :
    ((models event).bank side).direction ≠ 0 := by
  have first := (T).pairedComplex.boundaryChainRoll_edge_ne_zero
    ChainAt[contour,starts,event.val,event.property.1,LengthAt[contour,event],SpanAt[contour,event]]
    (Fin.last LengthAt[contour,event])
  cases side
  · exact first
  · exact (BankAt[contour,starts,event]).openings_direction_ne_zero _ first

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- The actual attachment parameter spaces retain their original interval or half-line metric. -/
instance compatibleContourBankParameterMetricSpace (bank : Attachment) : MetricSpace
    (K.compatibleContourBankParameter compact nonempty R no_boundary level higher M positive
      inner_disk beta acute bank) := by
  cases bank <;> dsimp only [compatibleContourBankParameter] <;> infer_instance

/-- Every actual roof attachment curve is a closed embedding on its entire original domain. -/
theorem compatibleContourBaseMark_isClosedEmbedding (bank : Attachment) (side : Bool) :
    Topology.IsClosedEmbedding (Base bank side) := by
  cases bank with
  | inl vertex =>
    exact Dilation.isClosedEmbedding
      (K.compatibleContourParentDilation compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W vertex.val vertex.property side)
  | inr edge =>
    exact Dilation.isClosedEmbedding
      (K.compatibleContourTailDilation compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W edge side)

/-- Every actual gap attachment curve is closed, retaining finite endpoints and infinite tails. -/
theorem compatibleContourGapMark_isClosedEmbedding (bank : Attachment)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ Stack bank) (side : Bool) :
    Topology.IsClosedEmbedding (Gap bank event member side) := by
  cases bank with
  | inl vertex =>
    unfold compatibleContourGapMark compatibleContourGapEdgeMark
    exact (models event).edgePoint_isClosedEmbedding side _
      (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts models event side _)
  | inr edge =>
    exact (models event).tailPoint_isClosedEmbedding side
      (K.compatibleContourGapBank_direction_ne_zero compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts models event side)

end Unfoldings.ConvexRoof
