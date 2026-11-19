module

public import Unfoldings.Roof.CompatibleContourFiniteMarkUniqueness
public import Unfoldings.Roof.CompatibleContourTerminalSeamClasses
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks

/-! Ordinary source-only slit marks keep their original side, attachment, and time. -/

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

local instance sourceOnlySmoothMarkIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
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

local instance sourceOnlySmoothMarkWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t
local notation "Regular" => K.compatibleContourBankParameterInterior compact nonempty R
  no_boundary level higher M positive inner_disk beta acute

variable (geometry : ∀ event :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour, OrientedBankGap
  (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts event)
  (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts event))

include geometry

private theorem sourceOnlyGapMark_eq_of_regular
    (bank other : Attachment) (event : Event) (member : event ∈ Stack bank)
    (other_mem : event ∈ Stack other) (side other_side : Bool)
    (t : ParamAt bank) (s : ParamAt other) (regular : Regular bank t)
    (equal : Gap other event other_mem other_side s = Gap bank event member side t) :
    other_side = side ∧ (⟨other, s⟩ : Σ b, ParamAt b) = ⟨bank, t⟩ := by
  have value (b : Attachment) (h : event ∈ Stack b) (flag : Bool) (u : ParamAt b) :
      (Gap b event h flag u).val =
        ((models event).addressFrontier (!flag) AddressAt[b,event,h,u]).val :=
    K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts models b event h flag u
  have position : (models event).addressFrontier (!other_side) AddressAt[other,event,other_mem,s] =
      (models event).addressFrontier (!side) AddressAt[bank,event,member,t] :=
    Subtype.ext ((value other other_mem other_side s).symm.trans
      ((congrArg PolygonalPoint.val equal).trans (value bank member side t)))
  have address : (!other_side) = (!side) ∧
      AddressAt[other,event,other_mem,s] = AddressAt[bank,event,member,t] := by
    cases bank with
    | inl v =>
      exact (models event).addressFrontier_eq_edge_interior (geometry event)
        (K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts models event)
        _ _ _ regular _ _ position
    | inr edge =>
      exact (models event).addressFrontier_eq_tail_positive (geometry event)
        _ _ regular _ _ position
  have flag : other_side = side := by
    simpa only [Bool.not_not] using congrArg Bool.not address.1
  refine ⟨flag, ?_⟩
  exact K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour event bank other member other_mem t s address.2

/-- Both the positive tail and strict finite-edge marks are unique in the actual
source-only graft, including when an attachment has no gaps. -/
theorem compatibleContourSourceOnlyMarks_unique
    (bank : Attachment) (t : ParamAt bank) (regular : Regular bank t) :
    MetricGluing.BankStackUniqueMarksAt Stack Pieces Base Gap bank t := by
  constructor
  · intro side other other_side s equal
    -- The roof marks are the original whole-cut marks in either graft.
    cases bank with
    | inl vertex =>
      cases other with
      | inl other =>
        have named := K.compatibleContourParentMark_eq_interior compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W vertex other side
          other_side t s regular equal
        have location := congrArg Prod.fst named
        have flags := congrArg (fun p => p.2.1) named
        have time := congrArg (fun p => p.2.2) named
        dsimp only at location flags time
        subst other
        subst s
        exact ⟨flags, rfl⟩
      | inr edge =>
        exact (K.compatibleContourTerminalMark_ne_parent_interior compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W edge other_side s
          vertex.val vertex.property side t regular.2 equal).elim
    | inr edge =>
      cases other with
      | inl v =>
        exact (K.compatibleContourParentMark_ne_terminal_positive compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W v.val v.property
          other_side s edge side t regular equal).elim
      | inr other =>
        have named := K.compatibleContourTerminalMark_eq compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W edge other side other_side
          t s equal
        have location := congrArg Prod.fst named
        have flags := congrArg (fun p => p.2.1) named
        have time := congrArg (fun p => p.2.2) named
        dsimp only at location flags time
        subst other
        subst s
        exact ⟨flags, rfl⟩
  · intro event member side other other_mem other_side s equal
    exact sourceOnlyGapMark_eq_of_regular K compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts models geometry bank other event member other_mem
      side other_side t s regular equal

end Unfoldings.ConvexRoof
