module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftCollapse
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks
public import Unfoldings.Roof.CompatibleContourPhysicalAttachments
public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Metric.BankStackSlotCases

/-! Original addresses and endpoints of the actual physical collapse fibers. -/

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

local instance sourceOnlyCollapseNamesIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyCollapseNamesWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourSourceOnlyCellInner compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourSourceOnlyCellCoordinates compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Label" => Space ⊕ (Event × ℂ)
local notation "CellLabel" => K.compatibleContourSourceOnlyCellLabel compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- Every original gap address is realized by its actual finite or infinite attachment. -/
theorem exists_compatibleContourGapAddress_eq (e : Event)
    (a₀ : PolygonalRay.Address (LengthAt[e] + 1)) :
    ∃ (b : Attachment) (member : e ∈ Stack b) (t : ParamAt b), AddressAt[b,e,member,t] = a₀ := by
  cases a₀ with
  | inl finite =>
    obtain ⟨i, t⟩ := finite
    obtain ⟨v, nonroot, mem, name⟩ := (D).exists_contourGapBankIndex_eq Selection contour e i
    let b : Attachment := .inl ⟨v, nonroot⟩
    have present : e ∈ Stack b := ((D).mem_contourSavedGapStack Selection contour v e).mpr
      (((D).mem_contourEdgeGapStack Selection contour v e).mp mem)
    exact ⟨b, present, t, congrArg (fun j => Sum.inl (j, t)) name⟩
  | inr t =>
    obtain ⟨b, mem⟩ := (D).exists_contourTerminalEdge_mem_gapStack Selection contour e
    exact ⟨.inr b, mem, t, rfl⟩

/-- The gap point named by the literal attachment and side is the corresponding marked fiber end. -/
theorem compatibleContourSourceOnlyGapMark_eq_intrinsicAddress
    (b : Attachment) (e : Event) (member : e ∈ Stack b) (flag : Bool) (t : ParamAt b) :
    Gap b e member flag t = (models e).intrinsicAddressPoint (!flag) AddressAt[b,e,member,t] :=
  PolygonalPoint.ext (K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models b e member flag t)

set_option maxHeartbeats 900000 in
-- Bank labels carry the dependent original piece indices.
/-- A whole-graft collapse with the prescribed boundary values takes every named
mark to the physical point of its original attachment. -/
theorem compatibleContourSourceOnlyCollapse_mark_horizontal
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (f : Graft → Space)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (addr : Addr) (valid : Valid addr) :
    Cap.horizontal (f (Point (Mark addr valid))) = Phys addr.1 addr.2.2.2 := by
  obtain ⟨bank, piece, flag, t⟩ := addr
  cases piece with
  | none =>
    have value := K.compatibleContourSourceOnlyBaseMark_label compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models bank flag t
    have same : (W.partition.restoreCut R.carrier (Base bank flag t)).val =
        (W.partition.restoreCut R.carrier (Base bank false t)).val := Sum.inl.inj value
    change Cap.horizontal (f (Point ⟨none, Base bank flag t⟩)) = _
    exact congrArg Cap.horizontal ((roof (Base bank flag t)).trans same)
  | some e =>
    change e ∈ Stack bank at valid
    let y := Gap bank e valid flag t
    have at_addr := K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models bank e valid flag t
    have bound : y.val ∈ frontier (models e).region :=
      at_addr.symm ▸ ((models e).addressFrontier (!flag) AddressAt[bank,e,valid,t]).property
    have value := K.compatibleContourSourceOnlyGapMark_label compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W models bank e (geometry e)
      valid flag t
    change MetricGluing.partialLabel (frontier (models e).region)
      (fun z => (FoldAt[e] z).val) e y.val =
      .inl (W.partition.restoreCut R.carrier (Base bank false t)).val at value
    rw [MetricGluing.partialLabel_of_mem _ _ _ _ bound] at value
    change Cap.horizontal (f (Point ⟨some e, y⟩)) = _
    exact congrArg Cap.horizontal ((boundary_gap e y bound).trans (Sum.inl.inj value))

end Unfoldings.ConvexRoof
