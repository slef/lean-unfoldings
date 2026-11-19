module

public import Unfoldings.Roof.CompatibleContourGapInteriorCharts
public import Unfoldings.Roof.CompatibleContourMarkCarrier
public import Unfoldings.Metric.BallIsometry

/-! Original whole roof balls survive grafting away from the actual forest carrier. -/

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

local instance contourRoofExcisionMeshFintype : Fintype (T).Index :=
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

local instance contourRoofExcisionWholeFintype : Fintype W.Index := W.finiteIndex

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

local notation "Original" => K.compatibleContourInternalCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Internal coordinate replacement preserves each original named cell point. -/
theorem compatibleContourInternalCoordinates_point (i) (j : Index i) (p : Cells i j) :
    Original i (MetricGluing.of _ (Internal i).relation j p) =
      Coordinates i (MetricGluing.of _ (Inner i) j p) := rfl

/-- Actual bank attachments have spatial labels on the original physical forest carrier. -/
theorem compatibleContourBankSeams_carrier_label
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (joined : (BankSeams).relation x y) :
    ∃ p : Space, CellLabel x = Sum.inl p ∧ Cap.horizontal p ∈ R.carrier := by
  obtain ⟨slot, t, first, _⟩ :=
    (K.compatibleContourBankClosedSeams_relation compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models x y).mp joined
  have label := MetricGluing.bankStackLeft_label Pieces Stack Base Gap PointLabel BankLabel
    (K.compatibleContourBaseMark_label compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)
    (fun bank event member side t => K.compatibleContourGapMark_label compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W models bank event
        (geometry event) member side t) slot t
  refine ⟨_, (congrArg PointLabel first).trans label, ?_⟩
  rcases slot with ⟨bank, index⟩
  cases bank with
  | inl vertex =>
    exact K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W vertex.val vertex.property false t
  | inr edge =>
    exact K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge false t

/-- Removing all bank attachments preserves a whole roof ball away from the physical forest.
This includes original roof cell seams and unbounded roof cells. -/
theorem compatibleContourRoofOutside_forgetChart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (j : Index none) (p : Cells none j)
    (outside : Cap.horizontal (W.partition.cellIsometryEquiv j p).val ∉ R.carrier) :
    Nonempty (MetricGluing.ForgetChart (MetricGluing.NestedCell (fun i j => Cells i j))
      (K.compatibleContourInternalGlue_included compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models) ⟨⟨none, j⟩, p⟩) := by
  apply (InternalSeams).exists_forgetChart_sum_of_label BankSeams CellLabel
    (fun x y joined => K.compatibleContourCellLabel_seam compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry x y
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mp joined))
    (fun label => ∃ q : Space, label = Sum.inl q ∧ Cap.horizontal q ∈ R.carrier)
    (K.compatibleContourBankSeams_carrier_label compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry) _
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry _) ?_
  rintro ⟨q, equal, on_cut⟩
  have original : CellLabel ⟨⟨none, j⟩, p⟩ =
      Sum.inl (W.partition.cellIsometryEquiv j p).val := rfl
  have position := Sum.inl.inj (original.symm.trans equal)
  exact outside (position.symm ▸ on_cut)

/-- A whole local ball of the original unbounded roof cut has exactly the full graft metric. -/
theorem compatibleContourGraft_roof_cell_ball
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (j : Index none) (p : Cells none j)
    (outside : Cap.horizontal (W.partition.cellIsometryEquiv j p).val ∉ R.carrier) :
    ∃ r : ℝ, 0 < r ∧ Nonempty
      (Metric.eball (Original none (MetricGluing.of _ (Internal none).relation j p))
        (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models
        (MetricGluing.of _ (Seams).relation ⟨none, j⟩ p)) (ENNReal.ofReal r)) := by
  obtain ⟨C⟩ := K.compatibleContourRoofOutside_forgetChart compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry j p outside
  let piece := K.compatibleContourInternalPieceBall compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models none j p C.radius
  exact ⟨C.radius, C.positive, ⟨(piece.symm.trans C.chart).trans
    (isometryEquivEBall (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models)
      (MetricGluing.of _ (Seams).relation ⟨none, j⟩ p) (ENNReal.ofReal C.radius))⟩⟩

end Unfoldings.ConvexRoof
