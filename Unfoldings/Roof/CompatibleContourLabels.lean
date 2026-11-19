module

public import Unfoldings.Roof.CompatibleContourPhysicalTails
public import Unfoldings.Roof.CompatibleContourClosedSeams
public import Unfoldings.Metric.BankStackLabels
public import Unfoldings.Metric.FinitePartialLabels
public import Unfoldings.Metric.FiniteLabelClasses

/-! Conserved original spatial labels prove finite classes for the actual graft seams. -/

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

local instance contourLabelMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e

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

local instance contourLabelWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

local notation "FoldAt[" e "]" => K.compatibleContourGapFrontierMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts models e

local notation "IndexAt[" vertex "," nonroot "," event "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour vertex nonroot event
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour vertex event)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour vertex event) member))

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour

/-- Physical bank points share their original spatial label. All remaining gap points
retain both their original gap tag and original coordinate. -/
abbrev compatibleContourLabel := Space ⊕ (Event × ℂ)

local notation "LabelType" => K.compatibleContourLabel compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour

/-- Extend the constructed physical frontier maps to every actual intrinsic piece point. -/
def compatibleContourPieceLabel : ∀ i, Pieces i → LabelType
  | none => fun p => .inl (W.partition.restoreCut R.carrier p).val
  | some event => fun p => MetricGluing.partialLabel (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event p.val

local notation "PieceLabel" => K.compatibleContourPieceLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models

/-- Keep the original intrinsic piece tag when evaluating its label. -/
def compatibleContourPointLabel (x : MetricGluing.Total Pieces) : LabelType :=
  PieceLabel x.1 x.2

local notation "PointLabel" => K.compatibleContourPointLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models

/-- The actual label of every raw original roof/gap cell representative. -/
def compatibleContourCellLabel
    (x : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j))) : LabelType :=
  PointLabel (MetricGluing.mappedNestedPoint Cells Inner Coordinates x)

/-- Each original finite or whole-tail bank has its literal physical roof label. -/
def compatibleContourBankLabel (bank : Attachment) (t : ParamAt bank) : LabelType :=
  .inl (W.partition.restoreCut R.carrier (Base bank false t)).val

local notation "BankLabel" => K.compatibleContourBankLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models

/-- Both original roof sides have the same physical label at every finite or infinite parameter. -/
theorem compatibleContourBaseMark_label (bank : Attachment) (side : Bool) (t : ParamAt bank) :
    PointLabel ⟨none, Base bank side t⟩ = BankLabel bank t := by
  apply congrArg Sum.inl
  cases bank with
  | inl vertex =>
    exact (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W vertex.val vertex.property side
        t).trans
      (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W vertex.val vertex.property false t).symm
  | inr edge =>
    exact (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side t).trans
      (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge false t).symm

/-- Each actual inserted gap bank retains the same physical label as its original roof bank. -/
theorem compatibleContourGapMark_label (bank : Attachment) (event : Event)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (member : event ∈ Stack bank) (side : Bool) (t : ParamAt bank) :
    PointLabel ⟨some event, Gap bank event member side t⟩ = BankLabel bank t := by
  cases bank with
  | inl vertex =>
    let addr : PolygonalRay.Address (LengthAt[contour,event] + 1) :=
      .inl (IndexAt[vertex.val,vertex.property,event,member], t)
    let boundary := (models event).addressFrontier side addr
    exact (MetricGluing.partialLabel_of_mem (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event boundary.val boundary.property).trans
      (congrArg Sum.inl (K.compatibleContourGapFrontierMap_edge compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W models vertex.val
          vertex.property event geometry member side t))
  | inr edge =>
    let boundary := (models event).addressFrontier side (.inr t)
    exact (MetricGluing.partialLabel_of_mem (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event boundary.val boundary.property).trans
      (congrArg Sum.inl (K.compatibleContourGapFrontierMap_tail compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W models edge event geometry
          member side t))

end Unfoldings.ConvexRoof
