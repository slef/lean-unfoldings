module

public import Unfoldings.Roof.CompatibleContourCellEmbeddings
public import Unfoldings.Roof.CompatibleContourBankEmbeddings
public import Unfoldings.Metric.BankStackCurveMetric
public import Unfoldings.Metric.ClosedBankCellSeams

/-! Every actual graft cell has a closed, isometric inclusion in its original intrinsic piece. -/

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

local instance contourBankClosedMeshFintype : Fintype (T).Index :=
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

local instance contourBankClosedWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

/-- Both original sides of every actual attachment have the same whole-domain distances. -/
theorem compatibleContourBaseMark_metric (bank : Attachment) (side : Bool)
    (s t : ParamAt bank) : edist (Base bank side s) (Base bank side t) =
      edist (Base bank false s) (Base bank false t) := by
  cases bank with
  | inl vertex =>
    cases side
    · rfl
    · exact (K.edist_compatibleContourParentMark_sides compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W vertex.val
        vertex.property s t).symm
  | inr edge =>
    exact (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side s t).trans
      (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W edge false s t).symm

/-- Every actual gap attachment has the common metric of its original roof bank. -/
theorem compatibleContourGapMark_metric (bank : Attachment)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ Stack bank) (side : Bool) (s t : ParamAt bank) :
    edist (Gap bank event member side s) (Gap bank event member side t) =
      edist (Base bank false s) (Base bank false t) := by
  cases bank with
  | inl vertex =>
    exact K.edist_compatibleContourGapEdgeMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models vertex.val vertex.property
      event member side s t
  | inr edge =>
    exact K.edist_compatibleContourGapTail compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models edge event member side s t

local notation "LP" => MetricGluing.bankStackLeftPiece Stack Pieces Base Gap
local notation "RP" => MetricGluing.bankStackRightPiece Stack Pieces Base Gap
local notation "LC" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap
local notation "RC" => MetricGluing.bankStackRightCurve Stack Pieces Base Gap

/-- Actual original embeddings construct all geometric data for each bank-cell attachment. -/
def compatibleContourBankCellPair (slot : MetricGluing.BankStackSlot Stack)
    (l : Index (LP slot)) (r : Index (RP slot)) :
    MetricGluing.BankCellPairData (Cells (LP slot) l) (Cells (RP slot) r) where
  Parameter := ParamAt slot.1
  LeftSpace := Pieces (LP slot)
  RightSpace := Pieces (RP slot)
  leftCell p := Coordinates (LP slot)
    (MetricGluing.of (fun j => Cells (LP slot) j) (Inner (LP slot)) l p)
  rightCell p := Coordinates (RP slot)
    (MetricGluing.of (fun j => Cells (RP slot) j) (Inner (RP slot)) r p)
  left_isometry := K.compatibleContourCellCoordinates_isometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models _ l
  right_isometry := K.compatibleContourCellCoordinates_isometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models _ r
  left_closed := (K.compatibleContourCellCoordinates_isClosedEmbedding compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models _
      l).isClosed_range
  right_closed := (K.compatibleContourCellCoordinates_isClosedEmbedding compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models _
      r).isClosed_range
  leftBank := LC slot
  rightBank := RC slot
  left_bank_closed := MetricGluing.bankStackLeftCurve_closed Stack Pieces Base Gap
    (K.compatibleContourBaseMark_isClosedEmbedding compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models)
    (K.compatibleContourGapMark_isClosedEmbedding compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models) slot
  right_bank_closed := MetricGluing.bankStackRightCurve_closed Stack Pieces Base Gap
    (K.compatibleContourBaseMark_isClosedEmbedding compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models)
    (K.compatibleContourGapMark_isClosedEmbedding compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models) slot
  same_metric := MetricGluing.bankStackCurves_same_metric Stack Pieces Base Gap
    (K.compatibleContourBaseMark_metric compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (K.compatibleContourGapMark_metric compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models) slot

/-- Every consecutive attachment and every pair of its original cell representatives. -/
abbrev compatibleContourBankCellSeam :=
  Σ slot : MetricGluing.BankStackSlot Stack, Index (LP slot) × Index (RP slot)

/-- The actual finite and infinite bank attachments now have constructed finite closed domains.
This is the bank part of the full graft relation; original internal seams are separate. -/
def compatibleContourBankClosedSeams :
    MetricGluing.ClosedSeams (MetricGluing.NestedCell (fun i j => Cells i j)) :=
  MetricGluing.ClosedSeams.ofBankCellPairs _
    (fun b : K.compatibleContourBankCellSeam compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models => ⟨LP b.1, b.2.1⟩)
    (fun b => ⟨RP b.1, b.2.2⟩)
    (fun b => K.compatibleContourBankCellPair compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models b.1 b.2.1 b.2.2)

/-- The constructed closed bank seams retain exactly the original marked-bank attachments.
All representatives in all original cells are retained in both directions. -/
theorem compatibleContourBankClosedSeams_relation
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j))) :
    (K.compatibleContourBankClosedSeams compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models).relation x y ↔
    MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
      (MetricGluing.bankStackRight Pieces Stack Base Gap)
      (MetricGluing.mappedNestedPoint Cells Inner Coordinates x)
      (MetricGluing.mappedNestedPoint Cells Inner Coordinates y) := by
  constructor
  · rintro ⟨b, p, rfl, rfl⟩
    obtain ⟨t, first, second⟩ := p.property
    refine ⟨b.1, t, ?_, ?_⟩
    · exact (congrArg (Sigma.mk (LP b.1)) first).trans
        (MetricGluing.bankStackLeft_curve Stack Pieces Base Gap b.1 t).symm
    · exact (congrArg (Sigma.mk (RP b.1)) second).trans
        (MetricGluing.bankStackRight_curve Stack Pieces Base Gap b.1 t).symm
  · rintro ⟨slot, t, first, second⟩
    obtain ⟨⟨i, j⟩, p⟩ := x
    obtain ⟨⟨k, l⟩, q⟩ := y
    have left_named := first.trans
      (MetricGluing.bankStackLeft_curve Stack Pieces Base Gap slot t)
    have right_named := second.trans
      (MetricGluing.bankStackRight_curve Stack Pieces Base Gap slot t)
    have left_index : i = LP slot := congrArg Sigma.fst left_named
    have right_index : k = RP slot := congrArg Sigma.fst right_named
    subst i
    subst k
    have left_value : Coordinates (LP slot)
        (MetricGluing.of (fun j => Cells (LP slot) j) (Inner (LP slot)) j p) = LC slot t :=
      eq_of_heq (Sigma.mk.inj_iff.mp left_named).2
    have right_value : Coordinates (RP slot)
        (MetricGluing.of (fun j => Cells (RP slot) j) (Inner (RP slot)) l q) = RC slot t :=
      eq_of_heq (Sigma.mk.inj_iff.mp right_named).2
    exact ⟨⟨slot, j, l⟩, ⟨(p, q), t, left_value, right_value⟩, rfl, rfl⟩

end Unfoldings.ConvexRoof
