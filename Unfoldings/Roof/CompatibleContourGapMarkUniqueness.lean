module

public import Unfoldings.Roof.CompatibleContourBankEmbeddings
public import Unfoldings.Geometry.BankGapAddressUniqueness

/-! Actual nonvertex gap marks uniquely retain their original forest attachment labels. -/

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

local instance contourGapMarkMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e

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

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Parameter" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour

/-- The original edge-and-parameter or true-tail address of an actual gap attachment. -/
def compatibleContourGapAddress (bank : Attachment)
    (event : (D).PositiveContourSource Selection contour) (member : event ∈ Stack bank)
    (t : Parameter bank) : PolygonalRay.Address (LengthAt[contour,event] + 1) :=
  match bank with
  | .inl vertex => .inl
      ((D).contourGapBankIndex Selection contour vertex.val vertex.property event
        (((D).mem_contourEdgeGapStack Selection contour vertex.val event).mpr
          (((D).mem_contourSavedGapStack Selection contour vertex.val event).mp member)), t)
  | .inr _ => .inr t

local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- The address retains the actual attachment label even when several original edges
occur along the same gap bank. The two sides use the same address convention. -/
theorem compatibleContourGapAddress_eq
    (event : (D).PositiveContourSource Selection contour)
    (bank other : Attachment) (member : event ∈ Stack bank) (other_member : event ∈ Stack other)
    (t : Parameter bank) (s : Parameter other)
    (equal : AddressAt[other,event,other_member,s] = AddressAt[bank,event,member,t]) :
    (⟨other, s⟩ : Σ b, Parameter b) = ⟨bank, t⟩ := by
  cases bank with
  | inl vertex =>
    cases other with
    | inl other =>
      have named := Prod.mk.inj (Sum.inl.inj equal)
      have original := (D).contourGapBankIndex_original Selection contour vertex.val vertex.property
        event (((D).mem_contourEdgeGapStack Selection contour vertex.val event).mpr
          (((D).mem_contourSavedGapStack Selection contour vertex.val event).mp member))
      have other_original := (D).contourGapBankIndex_original Selection contour other.val
        other.property event (((D).mem_contourEdgeGapStack Selection contour other.val event).mpr
          (((D).mem_contourSavedGapStack Selection contour other.val event).mp other_member))
      have vertex_eq : other = vertex := Subtype.ext
        (other_original.symm.trans ((congrArg
          (fun i : Fin (LengthAt[contour,event] + 1) => (Fcut).parents.parent^[i.val]
            ((D).positiveContourVertex Selection contour event)) named.1).trans original))
      subst other
      exact congrArg (fun u : unitInterval => (⟨.inl vertex, u⟩ : Σ b, Parameter b)) named.2
    | inr other => cases equal
  | inr edge =>
    cases other with
    | inl other => cases equal
    | inr other =>
      have parameter := Sum.inr.inj equal
      have original := (D).contourGap_last_child Selection contour edge event
        (((D).mem_contourEdgeGapStack Selection contour edge.val event).mpr
          (((D).mem_contourSavedGapStack Selection contour edge.val event).mp member))
      have other_original := (D).contourGap_last_child Selection contour other event
        (((D).mem_contourEdgeGapStack Selection contour other.val event).mpr
          (((D).mem_contourSavedGapStack Selection contour other.val event).mp other_member))
      have edge_eq : other = edge := Subtype.ext (other_original.symm.trans original)
      subst other
      exact congrArg (fun u : ℝ≥0 => (⟨.inr edge, u⟩ : Σ b, Parameter b)) parameter

/-- Strict finite-edge interiors and positive true-tail parameters exclude the original
vertices and the finite-to-infinite join, where multiple addresses are intentional. -/
def compatibleContourBankParameterInterior (bank : Attachment) (t : Parameter bank) : Prop :=
  match bank with
  | .inl _ => 0 < t ∧ t < 1
  | .inr _ => 0 < t

local notation "GapAt[" b "," e "," h "," side "," t "]" => K.compatibleContourGapMark compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W models
    b e h side t

/-- Every actual gap attachment uses exactly its original closed-edge or whole-tail address. -/
theorem compatibleContourGapMark_address (bank : Attachment)
    (event : (D).PositiveContourSource Selection contour) (member : event ∈ Stack bank)
    (side : Bool) (t : Parameter bank) :
    (GapAt[bank,event,member,side,t]).val =
      ((models event).bank side).addressPoint AddressAt[bank,event,member,t] := by
  cases bank <;> rfl

/-- At a nonvertex actual gap bank point there is precisely one attachment label,
side, and parameter. In particular, distinct edges and terminal rays cannot introduce
extra local bank seams. This is proved before forming the route-metric quotient. -/
theorem compatibleContourGapMark_eq_interior
    (event : (D).PositiveContourSource Selection contour)
    (geometry : OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (bank other : Attachment) (member : event ∈ Stack bank) (other_member : event ∈ Stack other)
    (side other_side : Bool) (t : Parameter bank) (s : Parameter other)
    (regular : K.compatibleContourBankParameterInterior compact nonempty R no_boundary level
      higher M positive inner_disk beta acute bank t)
    (equal : GapAt[other,event,other_member,other_side,s] = GapAt[bank,event,member,side,t]) :
    other_side = side ∧ (⟨other, s⟩ : Σ b, Parameter b) = ⟨bank, t⟩ := by
  have position : (models event).addressFrontier other_side AddressAt[other,event,other_member,s] =
      (models event).addressFrontier side AddressAt[bank,event,member,t] := by
    apply Subtype.ext
    exact (K.compatibleContourGapMark_address compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models other event other_member
        other_side s).symm.trans
      ((congrArg PolygonalPoint.val equal).trans
        (K.compatibleContourGapMark_address compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts W models bank event member side t))
  have unique : other_side = side ∧
      AddressAt[other,event,other_member,s] = AddressAt[bank,event,member,t] := by
    cases bank with
    | inl vertex =>
      exact (models event).addressFrontier_eq_edge_interior geometry
        (K.compatibleContourGapBank_edge_ne_zero compact nonempty R no_boundary level higher M
          positive inner_disk beta acute contour starts models event) _ _ _ regular _ _ position
    | inr edge =>
      exact (models event).addressFrontier_eq_tail_positive geometry _ _ regular _ _ position
  exact ⟨unique.1, K.compatibleContourGapAddress_eq compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour event bank other member other_member t s unique.2⟩

end Unfoldings.ConvexRoof
