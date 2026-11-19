module

public import Unfoldings.Roof.CompatibleContourSingleSlotGraft

/-! A subfamily of original bank slots is itself an exact original-piece graft. -/

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

local notation "inside" => K.compatible_section_interior compact nonempty R level higher M

local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourSelectedSlotMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut

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

local instance contourSelectedSlotWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Banks" => MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
  (MetricGluing.bankStackRight Pieces Stack Base Gap)

local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Original" => MetricGluing.mappedNestedPoint Cells Inner Coordinates
local notation "BankSeams" => K.compatibleContourBankClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "LP" => MetricGluing.bankStackLeftPiece Stack Pieces Base Gap

local notation "RP" => MetricGluing.bankStackRightPiece Stack Pieces Base Gap
local notation "LC" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap
local notation "RC" => MetricGluing.bankStackRightCurve Stack Pieces Base Gap
local notation "Internal" => K.compatibleContourInternalClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "ParamAt[" b "]" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute b

/-- Keep the entire original internal metric and a selected set of original bank slots. -/
def compatibleContourKeepBankSlots (keep : Set (MetricGluing.BankStackSlot Stack)) :
    (Seams).Seam → Prop
  | .inl _ => True
  | .inr bank => bank.1 ∈ keep

local notation "KeepAt[" keep "]" => K.compatibleContourKeepBankSlots compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models keep
local notation "ReducedAt[" keep "]" => MetricGluing.ClosedSeams.restrict Seams KeepAt[keep]
local notation "SelectedLeft[" keep "]" => fun (slot : Subtype (keep :
    Set (MetricGluing.BankStackSlot Stack)))
    (t : ParamAt[Sigma.fst (Subtype.val slot)]) =>
      MetricGluing.bankStackLeft Pieces Stack Base Gap (Subtype.val slot) t
local notation "SelectedRight[" keep "]" => fun (slot : Subtype (keep :
    Set (MetricGluing.BankStackSlot Stack)))
    (t : ParamAt[Sigma.fst (Subtype.val slot)]) =>
      MetricGluing.bankStackRight Pieces Stack Base Gap (Subtype.val slot) t
local notation "SelectedGlue[" keep "]" => MetricGluing.mappedBankGraftCells Cells Inner
  Coordinates SelectedLeft[keep] SelectedRight[keep]

/-- A restriction to original bank slots keeps every representative of those exact seams. -/
theorem compatibleContourSelectedSlots_relation (keep : Set (MetricGluing.BankStackSlot Stack))
    (x y : MetricGluing.Total Raw) :
    (ReducedAt[keep]).relation x y ↔ SelectedGlue[keep] x y := by
  constructor
  · rintro ⟨⟨seam, selected⟩, p, rfl, rfl⟩
    cases seam with
    | inl internal =>
      exact MetricGluing.NestedGlue.inside (E := fun i j => Cells i j) (inner := Inner)
        internal.1 _ _
        ((K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W models internal.1 _ _).mp
            ⟨internal.2, p, rfl, rfl⟩)
    | inr bank =>
      obtain ⟨slot, l, r⟩ := bank
      change slot ∈ keep at selected
      obtain ⟨t, first, last⟩ := p.property
      apply MetricGluing.NestedGlue.between
      refine ⟨⟨slot, selected⟩, t, ?_, ?_⟩
      · exact (congrArg (Sigma.mk (LP slot)) first).trans
          (MetricGluing.bankStackLeft_curve Stack Pieces Base Gap slot t).symm
      · exact (congrArg (Sigma.mk (RP slot)) last).trans
          (MetricGluing.bankStackRight_curve Stack Pieces Base Gap slot t).symm
  · intro joined
    cases joined with
    | «inside» i a b seam =>
      obtain ⟨s, p, first, last⟩ :=
        (K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W models i a b).mpr seam
      refine ⟨⟨.inl ⟨i, s⟩, trivial⟩, p, ?_, ?_⟩
      · exact congrArg (fun q : MetricGluing.Total (fun j => Cells i j) =>
          (⟨⟨i, q.1⟩, q.2⟩ : MetricGluing.Total Raw)) first
      · exact congrArg (fun q : MetricGluing.Total (fun j => Cells i j) =>
          (⟨⟨i, q.1⟩, q.2⟩ : MetricGluing.Total Raw)) last
    | between a b seam =>
      obtain ⟨⟨slot, member⟩, t, first, last⟩ := seam
      obtain ⟨⟨i, j⟩, p⟩ := x
      obtain ⟨⟨k, l⟩, q⟩ := y
      have left_named := first.trans
        (MetricGluing.bankStackLeft_curve Stack Pieces Base Gap slot t)
      have right_named := last.trans
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
      exact ⟨⟨.inr ⟨slot, j, l⟩, member⟩,
        ⟨(p, q), t, left_value, right_value⟩, rfl, rfl⟩

/-- Restricting original closed cell seams gives exactly the metric of the selected
whole original pieces attached along those bank slots. -/
def compatibleContourSelectedSlotsIsometry (keep : Set (MetricGluing.BankStackSlot Stack)) :
    MetricGluing.Realization Raw (ReducedAt[keep]).relation ≃ᵢ
      MetricGluing.BankGraft SelectedLeft[keep] SelectedRight[keep] :=
  (MetricGluing.changeSeamsIsometryEquiv Raw
    (fun x y joined => MetricGluing.point_eq_of_glue Raw
      ((K.compatibleContourSelectedSlots_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models keep x y).mp joined))
    (fun x y joined => MetricGluing.point_eq_of_glue Raw
      ((K.compatibleContourSelectedSlots_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models keep x y).mpr joined))).trans
    (MetricGluing.mappedBankGraftIsometry Cells Inner Coordinates
      SelectedLeft[keep] SelectedRight[keep])

end Unfoldings.ConvexRoof
