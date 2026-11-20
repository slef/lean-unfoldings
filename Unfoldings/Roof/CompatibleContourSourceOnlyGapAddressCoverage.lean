module

public import Unfoldings.Complex.ContourGapBankSurjectivity
public import Unfoldings.Roof.CompatibleContourSourceOnlyGapVertexMarks

/-! Every actual gap-frontier point belongs to a named finite or infinite attachment. -/

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

local instance sourceOnlyGapAddressCoverageFintype : Fintype (T).Index :=
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
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
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
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

/-- Every point of either gap frontier is one of the original stack marks. -/
theorem compatibleContourSourceOnlyGapMark_exists_of_frontier
    (e : Event) (x : PolygonalPoint (models e).region) (hx : x.val ∈ frontier (models e).region) :
    ∃ (bank : Attachment) (member : e ∈ Stack bank) (flag : Bool) (t : ParamAt bank),
      Gap bank e member flag t = x := by
  have on_bank : ∃ side : Bool, x.val ∈ ((models e).bank side).carrier := by
    rw [(models e).frontier_eq] at hx
    rcases hx with first | second
    · exact ⟨false, first⟩
    · exact ⟨true, second⟩
  obtain ⟨side, hs⟩ := on_bank
  obtain ⟨addr, named⟩ := ((models e).bank side).exists_address hs
  have physical (bank : Attachment) (member : e ∈ Stack bank) (t : ParamAt bank)
      (h : AddressAt[bank,e,member,t] = addr) : Gap bank e member (!side) t = x := by
    apply PolygonalPoint.ext
    have mark := K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models bank e member (!side) t
    rw [Bool.not_not, h] at mark
    exact mark.trans named
  cases addr with
  | inl et =>
    obtain ⟨i, t⟩ := et
    obtain ⟨v, nonroot, covered, hi⟩ := (D).exists_contourGapBankIndex_eq Selection contour e i
    let b : Attachment := .inl ⟨v, nonroot⟩
    have mem : e ∈ Stack b := ((D).mem_contourSavedGapStack Selection contour v e).mpr
      (((D).mem_contourEdgeGapStack Selection contour v e).mp covered)
    have at_index : AddressAt[b,e,mem,t] = .inl (i, t) :=
      congrArg (fun j => Sum.inl (j, t)) hi
    exact ⟨b, mem, !side, t, physical b mem t at_index⟩
  | inr t =>
    obtain ⟨b, member⟩ := (D).exists_contourTerminalEdge_mem_gapStack Selection contour e
    exact ⟨.inr b, member, !side, t, physical (.inr b) member t rfl⟩

end Unfoldings.ConvexRoof
