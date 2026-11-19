module

public import Unfoldings.Roof.CompatibleContourFiniteClasses
public import Unfoldings.Metric.ClosedSeamLabelExcision

/-! Whole metric balls inside actual gaps are unchanged by removing all bank attachments. -/

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

local instance contourInteriorExcisionMeshFintype : Fintype (T).Index :=
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

local instance contourInteriorExcisionWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "FoldAt[" e "]" => K.compatibleContourGapFrontierMap compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts models e

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour

local notation "LabelType" => K.compatibleContourLabel compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour
local notation "PieceLabel" => K.compatibleContourPieceLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "PointLabel" => K.compatibleContourPointLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "CellLabel" => K.compatibleContourCellLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "BankLabel" => K.compatibleContourBankLabel compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Glue" => K.compatibleContourCellGlue compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models
local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models

local notation "Internal" => K.compatibleContourInternalClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "InternalSeams" => MetricGluing.ClosedSeams.ofFamily
  (fun i j => Cells i j) Internal
local notation "BankSeams" => K.compatibleContourBankClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Removing all bank attachments retains exactly the original internal roof and gap seams. -/
abbrev compatibleContourInternalGlue := (InternalSeams).relation

/-- Every original internal seam is retained in the full actual closed-seam presentation. -/
theorem compatibleContourInternalGlue_included
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (joined : K.compatibleContourInternalGlue compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models x y) : (Seams).relation x y :=
  (InternalSeams).relation_included_sum BankSeams x y joined

/-- Every actual bank attachment carries an original physical spatial label. -/
theorem compatibleContourBankSeams_physical_label
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (joined : (BankSeams).relation x y) : ∃ p : Space, CellLabel x = Sum.inl p := by
  obtain ⟨slot, t, first, _⟩ :=
    (K.compatibleContourBankClosedSeams_relation compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models x y).mp joined
  have left_label := MetricGluing.bankStackLeft_label Pieces Stack Base Gap PointLabel BankLabel
    (K.compatibleContourBaseMark_label compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (fun bank event member side t => K.compatibleContourGapMark_label compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models bank event
        (geometry event) member side t) slot t
  exact ⟨_, (congrArg PointLabel first).trans left_label⟩

/-- At an actual gap interior point, removing every bank attachment preserves a whole
small metric ball. Internal cell seams and all original endpoint copies are retained. -/
theorem compatibleContourGapInterior_forgetChart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (event : Event) (j : Index (some event)) (p : Cells (some event) j)
    (interior_point : Complex.orthonormalBasisOneI.repr.symm p.val ∈
      interior (models event).region) :
    Nonempty (MetricGluing.ForgetChart (MetricGluing.NestedCell (fun i j => Cells i j))
      (K.compatibleContourInternalGlue_included compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models) ⟨⟨some event, j⟩, p⟩) := by
  apply (InternalSeams).exists_forgetChart_sum_of_label BankSeams CellLabel
    (fun x y joined => K.compatibleContourCellLabel_seam compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry x y
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mp joined))
    (fun label => ∃ q : Space, label = Sum.inl q)
    (K.compatibleContourBankSeams_physical_label compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry) _
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry _) ?_
  have nonphysical : CellLabel ⟨⟨some event, j⟩, p⟩ =
      Sum.inr (event, Complex.orthonormalBasisOneI.repr.symm p.val) := by
    change MetricGluing.partialLabel (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event (Complex.orthonormalBasisOneI.repr.symm p.val) = _
    unfold MetricGluing.partialLabel
    split
    · rename_i member
      exact (member.2 interior_point).elim
    · rfl
  rintro ⟨q, physical⟩
  have impossible := nonphysical.symm.trans physical
  contradiction

/-- Every representative of an interior gap point stays in that same original gap at
that same original coordinate, including representatives on internal cell seams. -/
theorem compatibleContourGapInterior_class_coordinate
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (event : Event) (j : Index (some event)) (p : Cells (some event) j)
    (interior_point : Complex.orthonormalBasisOneI.repr.symm p.val ∈
      interior (models event).region)
    (b : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (related : Relation.EqvGen (Seams).relation ⟨⟨some event, j⟩, p⟩ b) :
    ∃ (k : Index (some event)) (q : Cells (some event) k),
      b = ⟨⟨some event, k⟩, q⟩ ∧
      Complex.orthonormalBasisOneI.repr.symm q.val =
        Complex.orthonormalBasisOneI.repr.symm p.val := by
  have invariant := MetricGluing.label_eq_of_eqvGen (Seams).relation CellLabel
    (fun x y joined => K.compatibleContourCellLabel_seam compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry x y
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mp joined)) related
  have nonphysical : CellLabel ⟨⟨some event, j⟩, p⟩ =
      Sum.inr (event, Complex.orthonormalBasisOneI.repr.symm p.val) := by
    change MetricGluing.partialLabel (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event (Complex.orthonormalBasisOneI.repr.symm p.val) = _
    unfold MetricGluing.partialLabel
    split
    · rename_i member
      exact (member.2 interior_point).elim
    · rfl
  have named := invariant.symm.trans nonphysical
  obtain ⟨⟨i, k⟩, q⟩ := b
  cases i with
  | none =>
    change Sum.inl _ = Sum.inr _ at named
    contradiction
  | some other =>
    change MetricGluing.partialLabel (frontier (models other).region)
      (fun z => (FoldAt[other] z).val) other
      (Complex.orthonormalBasisOneI.repr.symm q.val) = Sum.inr _ at named
    unfold MetricGluing.partialLabel at named
    split at named
    · contradiction
    · have same := Sum.inr.inj named
      have tag : other = event := congrArg Prod.fst same
      subst other
      exact ⟨k, q, rfl, congrArg Prod.snd same⟩

end Unfoldings.ConvexRoof
