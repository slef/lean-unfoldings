module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks
public import Unfoldings.Geometry.BankGapJoinAddresses

/-! The true terminal gap joins retain the two original finite and infinite marks. -/

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

local instance sourceOnlyTerminalJoinMarkMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

local notation "BankAt[" q "," h "," e "]" =>
  K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive inner_disk
    beta acute q h e
local notation "OpenedAt[" q "," h "," e "]" =>
  K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive inner_disk
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

local instance sourceOnlyTerminalJoinMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun e : TriangleComplex.PositiveContourSource D Selection contour => BankGapModel.region (models e))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts models

local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection


local notation "Child[" e "]" => (Subtype.mk (Subtype.val e) (And.left (Subtype.property e)))
local notation "LastPair[" e "]" => (Sigma.mk (Sum.inl Child[e]) 1 : Σ b : Attachment, ParamAt b)
local notation "TailPair[" e "]" => (Sigma.mk (Sum.inr e) 0 : Σ b : Attachment, ParamAt b)

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- The literal gap join retains its side and only its original two adjacent addresses. -/
theorem compatibleContourSourceOnlyGapMark_eq_terminal_join
    (event : Event) (geometry : OrientedBankGap (BankAt[contour,starts,event])
      (OpenedAt[contour,starts,event]))
    (edge : Edge) (other : Attachment) (member : event ∈ Stack (.inr edge))
    (other_member : event ∈ Stack other) (side other_side : Bool) (s : ParamAt other)
    (equal : Gap other event other_member other_side s = Gap (.inr edge) event member side 0) :
    other_side = side ∧
      ((⟨other, s⟩ : Σ b, ParamAt b) = TailPair[edge] ∨
        (⟨other, s⟩ : Σ b, ParamAt b) = LastPair[edge]) := by
  have position : (models event).addressFrontier (!other_side) AddressAt[other,event,other_member,s] =
      (models event).addressFrontier (!side) (.inr 0) := by
    apply Subtype.ext
    exact (K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models other event other_member other_side
      s).symm.trans (congrArg PolygonalPoint.val equal)
  have named := (models event).addressFrontier_eq_tail_zero geometry
    (K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models event) (!side) (!other_side) _ position
  have flag : other_side = side := by
    simpa only [Bool.not_not] using congrArg Bool.not named.1
  refine ⟨flag, ?_⟩
  rcases named.2 with tail | last
  · exact Or.inl (K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour event (.inr edge) other member other_member 0 s tail)
  · let child : {v : (D).Vertex Set.univ // v ∉ (Fcut).parents.roots} := Child[edge]
    have last_member : event ∈ Stack (.inl child) := member
    have index : AddressAt[.inl child,event,last_member,1] =
        .inl (Fin.last ((D).positiveContourBankLength Selection contour event), 1) := by
      unfold compatibleContourGapAddress
      have at_edge := ((D).mem_contourEdgeGapStack Selection contour edge.val event).mpr
        (((D).mem_contourSavedGapStack Selection contour edge.val event).mp member)
      exact congrArg (fun i => Sum.inl (i, (1 : unitInterval)))
        ((D).contourGapBankIndex_last Selection contour edge event at_edge)
    exact Or.inr (K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour event (.inl child) other last_member other_member 1 s
      (last.trans index.symm))

end Unfoldings.ConvexRoof
