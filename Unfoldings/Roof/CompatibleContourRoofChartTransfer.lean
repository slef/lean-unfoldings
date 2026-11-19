module

public import Unfoldings.Roof.CompatibleContourRoofExcision
public import Unfoldings.Metric.LocalBallRegularity
public import Unfoldings.Metric.InternalFamilyBallCenters

/-! Intrinsic roof charts transfer through the actual graft ball comparison. -/

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

local instance contourRoofChartTransferMeshFintype : Fintype (T).Index :=
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

local instance contourRoofChartTransferWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- The actual internal piece-ball identification retains its named original center. -/
theorem compatibleContourInternalPieceBall_center (i) (j : Index i) (p : Cells i j)
    {r : ℝ} (positive_r : 0 < r) :
    (K.compatibleContourInternalPieceBall compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models i j p r
      ⟨MetricGluing.of _ (InternalSeams).relation ⟨i, j⟩ p,
        Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_r)⟩).val =
      Original i (MetricGluing.of _ (Internal i).relation j p) := by
  let F := MetricGluing.internalFamilyCellBall (fun i j => Cells i j) Internal i j p r
  let root : Metric.eball (MetricGluing.of _ (Internal i).relation j p) (ENNReal.ofReal r) :=
    ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_r)⟩
  let raw : Metric.eball (MetricGluing.of _ (InternalSeams).relation ⟨i, j⟩ p)
      (ENNReal.ofReal r) := ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive_r)⟩
  have centered : F root = raw := Subtype.ext
    (MetricGluing.internalFamilyCellBall_center (fun i j => Cells i j) Internal i j p positive_r)
  have backward : F.symm raw = root :=
    (congrArg F.symm centered).symm.trans (F.symm_apply_apply root)
  exact congrArg (fun z => Original i z.val) backward

/-- Every existing intrinsic roof planar chart outside the actual physical forest
transfers to a whole planar chart in the actual graft. Intrinsic roof regularity is
an explicit input here; this theorem does not assert regularity at roof cone points. -/
theorem compatibleContourGraft_roof_chart_of_regular
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (j : Index none) (p : Cells none j)
    (outside : Cap.horizontal (W.partition.cellIsometryEquiv j p).val ∉ R.carrier)
    (regular : HasMetricBallChart Plane
      (Original none (MetricGluing.of _ (Internal none).relation j p))) :
    HasMetricBallChart Plane
      (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models
        (MetricGluing.of _ (Seams).relation ⟨none, j⟩ p)) := by
  obtain ⟨C⟩ := K.compatibleContourRoofOutside_forgetChart compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry j p outside
  let piece := K.compatibleContourInternalPieceBall compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models none j p C.radius
  let raw : Metric.eball (MetricGluing.of _ (InternalSeams).relation ⟨none, j⟩ p)
      (ENNReal.ofReal C.radius) :=
    ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  let root : Metric.eball (Original none (MetricGluing.of _ (Internal none).relation j p))
      (ENNReal.ofReal C.radius) :=
    ⟨_, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  have centered : piece raw = root := Subtype.ext
    (K.compatibleContourInternalPieceBall_center compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models none j p C.positive)
  have backward : piece.symm root = raw :=
    (congrArg piece.symm centered).symm.trans (piece.symm_apply_apply raw)
  let A := piece.symm.trans C.chart
  have center : (A root).val = MetricGluing.of _ (Seams).relation ⟨none, j⟩ p :=
    (congrArg (fun z => (C.chart z).val) backward).trans (C.agrees raw)
  exact (regular.of_centered_ball_equiv C.positive A center).isometryEquiv
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)

end Unfoldings.ConvexRoof
