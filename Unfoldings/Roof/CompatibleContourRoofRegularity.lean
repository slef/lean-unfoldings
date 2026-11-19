module

public import Unfoldings.Roof.CompatibleContourRoofChartTransfer
public import Unfoldings.Roof.CompatibleWholeCutRegularity

/-! Whole planar charts on the actual graft roof away from the physical forest. -/

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

local instance contourRoofRegularityMeshFintype : Fintype (T).Index :=
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

local instance contourRoofRegularityWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Name the original roof piece's identification with the original whole-cut roof metric. -/
def compatibleContourRoofPieceIsometry : Pieces none ≃ᵢ W.Cut := IsometryEquiv.refl _

local notation "RoofMetric" => K.compatibleContourRoofPieceIsometry compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- The roof-piece identification retains every original roof point. -/
theorem compatibleContourRoofPieceIsometry_apply (x : Pieces none) : RoofMetric x = x := rfl

/-- Original convex slope geometry derives whole planar charts at every actual roof
cell representative outside the forest. No intrinsic regularity certificate is supplied. -/
theorem compatibleContourGraft_roof_off_cut_chart (convex : Convex ℝ slopes)
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (j : Index none) (p : Cells none j)
    (off_cut : Cap.horizontal (W.partition.cellIsometryEquiv j p).val ∉ R.carrier) :
    HasMetricBallChart Plane
      (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models
        (MetricGluing.of _ (Seams).relation ⟨none, j⟩ p)) := by
  let x := Original none (MetricGluing.of _ (Internal none).relation j p)
  have original := K.compatibleContourInternalCoordinates_point compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models none j p
  have physical : (W.partition.restoreCut R.carrier (RoofMetric x)).val =
      (W.partition.cellIsometryEquiv j p).val :=
    congrArg (fun z : Pieces none => (W.partition.restoreCut R.carrier (RoofMetric z)).val) original
  have outside : Cap.horizontal (W.partition.restoreCut R.carrier (RoofMetric x)).val ∉
      R.carrier := by
    intro member
    exact off_cut ((congrArg Cap.horizontal physical) ▸ member)
  have roof_regular := K.compatibleWholeCut_off_cut_regular compact nonempty R no_boundary level
    higher M positive inner_disk beta acute W convex (RoofMetric x) outside
  have moved := roof_regular.isometryEquiv (RoofMetric).symm
  have regular : HasMetricBallChart Plane x :=
    Eq.mp (congrArg (HasMetricBallChart Plane) ((RoofMetric).symm_apply_apply x)) moved
  exact K.compatibleContourGraft_roof_chart_of_regular compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry j p off_cut regular

/-- Every intrinsic roof point outside the actual forest has a whole planar ball in the
graft, including unbounded roof points. No cell representative or local chart is input. -/
theorem compatibleContourGraft_roof_point_off_cut_chart (convex : Convex ℝ slopes)
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x : Pieces none)
    (off_cut : Cap.horizontal (W.partition.restoreCut R.carrier (RoofMetric x)).val ∉ R.carrier) :
    HasMetricBallChart Plane (MetricGluing.of Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap)) none x) := by
  obtain ⟨y, at_x⟩ := (Original none).surjective x
  obtain ⟨⟨j, p⟩, equal⟩ := MetricGluing.point_surjective (fun j => Cells none j)
    (Internal none).relation y
  have represented : Original none (MetricGluing.of _ (Internal none).relation j p) = x :=
    (congrArg (Original none) equal).trans at_x
  have at_cell := (K.compatibleContourInternalCoordinates_point compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models none j p).symm.trans
    represented
  have physical : (W.partition.cellIsometryEquiv j p).val =
      (W.partition.restoreCut R.carrier (RoofMetric x)).val :=
    congrArg (fun z : Pieces none => (W.partition.restoreCut R.carrier (RoofMetric z)).val) at_cell
  have outside : Cap.horizontal (W.partition.cellIsometryEquiv j p).val ∉ R.carrier := by
    intro member
    exact off_cut ((congrArg Cap.horizontal physical) ▸ member)
  have regular := K.compatibleContourGraft_roof_off_cut_chart compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models convex geometry j p outside
  have center := (K.compatibleContourClosedSeamIsometry_point compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models ⟨none, j⟩ p).trans
    (congrArg (MetricGluing.of Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap)) none) at_cell)
  exact Eq.mp (congrArg (HasMetricBallChart Plane) center) regular

end Unfoldings.ConvexRoof
