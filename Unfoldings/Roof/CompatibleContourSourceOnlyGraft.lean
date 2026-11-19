module

public import Unfoldings.Roof.CompatibleContourGraft
public import Unfoldings.Roof.CompatibleContourSourceOnlyGaps

/-! Assemble the saved-frontier gaps with complementary sides at the original roof banks. -/

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
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyContourGraftIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
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
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyContourGraftWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))

/-- A roof together with polygonal gaps, indexed by the same bank-stack tags. -/
def polygonalBankStackPiece {G : Type} (Roof : Type) (region : G → Set ℂ) :
    Option G → Type
  | none => Roof
  | some event => PolygonalPoint (region event)

instance {G : Type} (Roof : Type) [EMetricSpace Roof] (region : G → Set ℂ)
    (i : Option G) : EMetricSpace (polygonalBankStackPiece Roof region i) := by
  cases i <;> dsimp only [polygonalBankStackPiece] <;> infer_instance

local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))

/-- The original finite roof banks and their true infinite continuations. -/
def compatibleContourSourceOnlyBaseMark : ∀ bank : Attachment, Bool → ParamAt bank → W.Cut
  | .inl vertex, side, t => K.compatibleContourParentMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W vertex.val vertex.property side t
  | .inr edge, side, t => K.compatibleContourTerminalMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side t

/-- From the exit roof bank, the stack meets the right side of a gap first. That side
carries the complement of the saved exit angle. The stack order and arclength are unchanged. -/
def compatibleContourSourceOnlyGapMark (bank : Attachment) (event : Event)
    (member : event ∈ Stack bank) (side : Bool) (t : ParamAt bank) :
    PolygonalPoint (models event).region := by
  cases bank with
  | inl vertex =>
    exact (models event).edgePoint (!side) IndexAt[vertex.val,vertex.property,event,member] t
  | inr edge =>
    exact (models event).tailPoint (!side) t

local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

/-- The source-only saved-frontier graft identifies all consecutive original bank marks. -/
abbrev compatibleContourSourceOnlyGraft :=
  MetricGluing.BankStackGraft Pieces Stack Base Gap

/-- Source-only gaps meet their finite and infinite attachment domains at their actual rim mark. -/
theorem compatibleContourSourceOnlyGapMark_join
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : Event) (member : event ∈ Stack (.inr edge)) (side : Bool) :
    Gap (.inr edge) event member side 0 =
      Gap (.inl ⟨edge.val, edge.property.1⟩) event member side 1 := by
  let gap := models event
  change gap.tailPoint (!side) 0 = gap.edgePoint (!side)
    IndexAt[edge.val,edge.property.1,event,member] 1
  rw [gap.tailPoint_zero_eq_edgePoint]
  exact congrArg (fun i => gap.edgePoint (!side) i 1)
    ((D).contourGapBankIndex_last Selection contour edge event _).symm

local notation "BankLength[" v "," h "]" => TriangleComplex.boundaryBankLength D
  (TriangleComplex.contourParentBank D Selection contour (PotentialCutForest.boundary_roots Fcut)
    starts v h false)

/-- The parent edge's length is preserved by both literal banks of its source-only gap. -/
theorem compatibleContourSourceOnlyEdgeMetric
    (vertex : (T).pairedComplex.Vertex Set.univ) (nonroot : vertex ∉ (Fcut).parents.roots)
    (event : Event) (member : event ∈ Stack (.inl ⟨vertex, nonroot⟩))
    (side : Bool) (s t : unitInterval) :
    edist (Gap (.inl ⟨vertex, nonroot⟩) event member side s)
      (Gap (.inl ⟨vertex, nonroot⟩) event member side t) =
        ENNReal.ofReal BankLength[vertex,nonroot] * edist s t := by
  let k := IndexAt[vertex,nonroot,event,member]
  let B := BankAt[contour,starts,event]
  let κ := (D).interiorAngularDefect Set.univ VertexAt[contour,event]
  let N : BankGapModel B (B.openings [⟨0, κ⟩]) := models event
  have original := (D).contourGapBankIndex_original Selection contour vertex nonroot event
    (((D).mem_contourEdgeGapStack Selection contour vertex event).mpr
      (((D).mem_contourSavedGapStack Selection contour vertex event).mp member))
  have length := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts event k
  have named := congrArg (fun v : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots} =>
      BankLength[v.val,v.property])
    (show (⟨(Fcut).parents.parent^[k.val] VertexAt[contour,event],
      (Fcut).parents.iterate_lt_distanceToRoot_not_mem VertexAt[contour,event]
        (by rw [SpanAt[contour,event]]; exact k.isLt)⟩ :
        {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots}) = ⟨vertex, nonroot⟩ from
      Subtype.ext original)
  have coefficient : (‖B.chain.edge k‖₊ : ℝ≥0∞) = ENNReal.ofReal BankLength[vertex,nonroot] := by
    simpa only [ofReal_norm, enorm_eq_nnnorm] using congrArg ENNReal.ofReal (length.trans named)
  have first : edist (N.edgePoint false k s) (N.edgePoint false k t) =
      ENNReal.ofReal BankLength[vertex,nonroot] * edist s t :=
    (N.edist_edgePoint false k s t).trans (congrArg (fun r => r * edist s t) coefficient)
  cases side
  · exact (N.edist_edgePoint_sides k s t).symm.trans first
  · exact first

/-- The terminal tail is attached at the true constant speed of its last finite edge. -/
theorem compatibleContourSourceOnlyTailMetric
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : Event) (member : event ∈ Stack (.inr edge)) (side : Bool) (s t : ℝ≥0) :
    edist (Gap (.inr edge) event member side s) (Gap (.inr edge) event member side t) =
      ENNReal.ofReal BankLength[edge.val,edge.property.1] * edist s t := by
  let m := LengthAt[contour,event]
  let B := BankAt[contour,starts,event]
  let κ := (D).interiorAngularDefect Set.univ VertexAt[contour,event]
  let N : BankGapModel B (B.openings [⟨0, κ⟩]) := models event
  have index : IndexAt[edge.val,edge.property.1,event,member] = Fin.last m :=
    (D).contourGapBankIndex_last Selection contour edge event _
  have length := K.compatibleContourSourceOnlyEdgeMetric compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts models edge.val edge.property.1
      event member side 0 1
  change edist (N.edgePoint (!side) IndexAt[edge.val,edge.property.1,event,member] 0)
    (N.edgePoint (!side) IndexAt[edge.val,edge.property.1,event,member] 1) =
      ENNReal.ofReal BankLength[edge.val,edge.property.1] * edist (0 : unitInterval) 1 at length
  have unit : edist (0 : unitInterval) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num
  rw [index, unit, mul_one] at length
  exact (BankGapModel.edist_tailPoint_eq_last_edge (events := [⟨0, κ⟩]) N (!side) s t).trans
    (congrArg (fun d => d * edist s t) length)

/-- All finite and infinite source-only seams match the intrinsic roof-bank distances. -/
theorem compatibleContourSourceOnlyGapMark_metric (bank : Attachment)
    (event : Event) (member : event ∈ Stack bank) (side : Bool) (s t : ParamAt bank) :
    edist (Gap bank event member side s) (Gap bank event member side t) =
      edist (Base bank false s) (Base bank false t) := by
  cases bank with
  | inl v =>
    let original := (D).contourParentBank Selection contour (Fcut).boundary_roots starts
      v.val v.property false
    exact (K.compatibleContourSourceOnlyEdgeMetric compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models v.val v.property
      event member side s t).trans
        (((T).pairedFolding.edist_directedBoundaryPath_eq_length original s t).symm.trans
          (K.compatibleWholeMap_edist_bank compact nonempty R no_boundary level
            higher M positive inner_disk beta acute W original s t).symm)
  | inr e =>
    exact (K.compatibleContourSourceOnlyTailMetric compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts models e event member
      side s t).trans (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W e false s t).symm

end Unfoldings.ConvexRoof
