module

public import Unfoldings.Roof.CompatibleContourFiniteSeamExcision

/-! The restricted original cell model is exactly the graft along one whole bank pair. -/

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

local instance contourSingleSlotMeshFintype : Fintype (T).Index :=
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

local instance contourSingleSlotWholeFintype : Fintype W.Index := W.finiteIndex

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
local notation "KeepAt[" slot "]" => K.compatibleContourKeepBankSlot compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models slot
local notation "ReducedAt[" slot "]" => MetricGluing.ClosedSeams.restrict Seams KeepAt[slot]
local notation "SlotLeft[" slot "]" => fun (_ : Unit)
    (t : ParamAt[Sigma.fst (slot : MetricGluing.BankStackSlot Stack)]) =>
  MetricGluing.bankStackLeft Pieces Stack Base Gap slot t
local notation "SlotRight[" slot "]" => fun (_ : Unit)
    (t : ParamAt[Sigma.fst (slot : MetricGluing.BankStackSlot Stack)]) =>
  MetricGluing.bankStackRight Pieces Stack Base Gap slot t
local notation "SlotGlue[" slot "]" => MetricGluing.mappedBankGraftCells Cells Inner Coordinates
  SlotLeft[slot] SlotRight[slot]

/-- All original intrinsic pieces, with just the named whole bank pair attached.
The two endpoint curves may belong to the same original roof piece. -/
abbrev compatibleContourSingleSlotGraft (slot : MetricGluing.BankStackSlot Stack) :=
  MetricGluing.BankGraft SlotLeft[slot] SlotRight[slot]

/-- Restricting original cell seams to one slot keeps exactly the original whole-piece
graft along that bank pair, including internal seams and every closed endpoint. -/
theorem compatibleContourSingleSlot_relation (slot : MetricGluing.BankStackSlot Stack)
    (x y : MetricGluing.Total Raw) :
    (ReducedAt[slot]).relation x y ↔ SlotGlue[slot] x y := by
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
      obtain ⟨other, l, r⟩ := bank
      change other = slot at selected
      subst other
      obtain ⟨t, first, last⟩ := p.property
      apply MetricGluing.NestedGlue.between
      refine ⟨(), t, ?_, ?_⟩
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
      obtain ⟨⟨⟩, t, first, last⟩ := seam
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
      exact ⟨⟨.inr ⟨slot, j, l⟩, rfl⟩,
        ⟨(p, q), t, left_value, right_value⟩, rfl, rfl⟩

/-- The restricted actual cell metric is exactly the original intrinsic-piece graft
along the single named bank pair. No local chart or finite-class premise is needed. -/
def compatibleContourSingleSlotIsometry (slot : MetricGluing.BankStackSlot Stack) :
    MetricGluing.Realization Raw (ReducedAt[slot]).relation ≃ᵢ
      K.compatibleContourSingleSlotGraft compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models slot :=
  (MetricGluing.changeSeamsIsometryEquiv Raw
    (fun x y joined => MetricGluing.point_eq_of_glue Raw
      ((K.compatibleContourSingleSlot_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models slot x y).mp joined))
    (fun x y joined => MetricGluing.point_eq_of_glue Raw
      ((K.compatibleContourSingleSlot_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models slot x y).mpr joined))).trans
    (MetricGluing.mappedBankGraftIsometry Cells Inner Coordinates SlotLeft[slot] SlotRight[slot])

/-- Every original cell point keeps its literal intrinsic copy in the single-slot model. -/
theorem compatibleContourSingleSlotIsometry_point (slot : MetricGluing.BankStackSlot Stack)
    (a : MetricGluing.Total Raw) :
    K.compatibleContourSingleSlotIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models slot
      (MetricGluing.point Raw (ReducedAt[slot]).relation a) =
    MetricGluing.point Pieces (MetricGluing.bankSeams SlotLeft[slot] SlotRight[slot])
      (Original a) :=
  rfl

end Unfoldings.ConvexRoof
