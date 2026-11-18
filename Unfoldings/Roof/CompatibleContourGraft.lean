module

public import Unfoldings.Roof.CompatibleContourTailAgreement

/-! The actual complete roof-plus-gap graft, with every finite and infinite bank attachment. -/

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

local instance contourGraftIndexFintype : Fintype (T).Index :=
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

local instance contourGraftWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

/-- Retain separately every original finite parent edge and each true terminal continuation. -/
abbrev compatibleContourBankAttachment : Type :=
  {v : (T).pairedComplex.Vertex Set.univ // v ∉ (Fcut).parents.roots} ⊕
    (T).pairedComplex.ContourTerminalEdge (Fcut).selection

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

/-- Closed finite edges keep interval parameters; whole tails keep their nonnegative parameters. -/
abbrev compatibleContourBankParameter : Attachment → Type
  | .inl _ => unitInterval
  | .inr _ => ℝ≥0

local notation "Parameter" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

/-- Every attachment uses the actual ordered source stack on its named last or finite edge. -/
def compatibleContourBankStack : Attachment →
    List ((T).pairedComplex.PositiveContourSource (Fcut).selection contour)
  | .inl vertex => (T).pairedComplex.contourSavedGapStack (Fcut).selection contour vertex.val
  | .inr edge => (T).pairedComplex.contourSavedGapStack (Fcut).selection contour edge.val

local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W models

/-- The original roof marks are its literal finite cut banks and endpoint-determined tails. -/
def compatibleContourBaseMark : ∀ bank : Attachment, Bool → Parameter bank → Pieces none
  | .inl vertex, side, t => K.compatibleContourParentMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W vertex.val vertex.property side t
  | .inr edge, side, t => K.compatibleContourTerminalMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side t

/-- Every gap mark is on its actual canonical finite edge or its whole infinite bank tail. -/
def compatibleContourGapMark : ∀ (bank : Attachment)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour),
    event ∈ Stack bank → Bool → Parameter bank → Pieces (some event)
  | .inl vertex, event, member, side, t => K.compatibleContourGapEdgeMark compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts models vertex.val
        vertex.property event member side t
  | .inr _, event, _, side, t => (models event).tailPoint side t

local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- The actual original pieces and every consecutive finite or infinite attachment determine
this route metric. No nonoverlap, flatness or global injectivity is assumed. -/
abbrev compatibleContourGraft := MetricGluing.BankStackGraft Pieces Stack Base Gap

/-- The tail attachment starts at exactly the finite roof attachment's true endpoint copy. -/
theorem compatibleContourBaseMark_join
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection) (side : Bool) :
    Base (.inr edge) side 0 = Base (.inl ⟨edge.val, edge.property.1⟩) side 1 :=
  K.compatibleContourTerminalMark_zero compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts W edge side

/-- Finite and infinite gap seams share their literal canonical endpoint marks. -/
theorem compatibleContourGapMark_join
    (edge : (T).pairedComplex.ContourTerminalEdge (Fcut).selection)
    (event : (T).pairedComplex.PositiveContourSource (Fcut).selection contour)
    (member : event ∈ Stack (.inr edge)) (side : Bool) :
    Gap (.inr edge) event member side 0 =
      Gap (.inl ⟨edge.val, edge.property.1⟩) event member side 1 :=
  K.compatibleContourGapTail_join compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts models edge event member side

end Unfoldings.ConvexRoof
