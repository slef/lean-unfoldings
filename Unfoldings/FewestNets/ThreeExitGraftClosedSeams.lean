module

public import Unfoldings.FewestNets.ThreeExitGraftCells
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Metric.ClosedBankStackCells
public import Unfoldings.Metric.ClosedCoincidentSeams

/-! Every graft seam is a closed isometric identification of actual cells. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftSeamsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap

local notation "Index" => contourGraftCellIndex L S
local notation "Cells" => contourGraftCells L S
local notation "Inner" => contourGraftCellInner L S
local notation "Coordinates" => contourGraftCellCoordinates L S
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

theorem contourGraftCellCoordinates_isometry (i : Option Event) (j : Index i) :
    Isometry (fun p : Cells i j => Coordinates i
      (MetricGluing.of (fun j => Cells i j) (Inner i) j p)) := by
  cases i with
  | none => exact L.whole.partition.cut_cell_isometry R.wholeCarrier j
  | some e => exact Model[e].planarCell_intrinsic_isometry j

/-- The internal families retain the original graph-cut and gap seams. -/
def contourGraftInternalSeams : ∀ i, MetricGluing.ClosedSeams (fun j => Cells i j)
  | none => MetricGluing.ClosedSeams.reparametrize
      (L.whole.partition.cutPhysicalSeams R.wholeCarrier).offDiagonal.closedSeams
      L.whole.partition.cellIsometryEquiv
  | some e => MetricGluing.distinctCoincidentClosedSeams Model[e].planarCells
      Model[e].planarCells_closed

local notation "Internal" => contourGraftInternalSeams L S

/-- Assemble the closed internal seams and all consecutive bank slots. -/
def contourGraftClosedSeams : MetricGluing.ClosedSeams Raw := by
  letI : ∀ edge : Attachment, MetricSpace (Param edge) := contourAttachmentMetric S
  refine MetricGluing.bankStackClosedSeams Pieces Stack Base Gap Cells Inner Coordinates
    (L.contourGraftCellCoordinates_isometry S) (fun i j => (L.contourGraftCell_geometry S i j).1)
    (L.isClosedEmbedding_contourBaseMark S) (isClosedEmbedding_contourGapMark S)
    (L.edist_contourBaseMark_sides S) (L.edist_contourGapMark_eq_base S) Internal

local notation "Seams" => contourGraftClosedSeams L S

theorem contourGraftClosedSeams_relation (x y : MetricGluing.Total Raw) :
    (Seams).relation x y ↔ L.contourGraftCellGlue S x y := by
  let : ∀ edge : Attachment, MetricSpace (Param edge) := contourAttachmentMetric S
  unfold contourGraftClosedSeams
  apply MetricGluing.bankStackClosedSeams_relation
  intro i p q
  cases i with
  | none => exact MetricGluing.ClosedSeams.reparametrize_relation _ _ p q
  | some e =>
    exact MetricGluing.distinctCoincidentClosedSeams_relation
      (Model[e]).planarCells (Model[e]).planarCells_closed p q

/-- The closed seam presentation computes the same complete route distances. -/
def contourGraftClosedSeamsIsometry :
    MetricGluing.Realization Raw (Seams).relation ≃ᵢ L.contourGraft S :=
  (MetricGluing.changeSeamsIsometryEquiv Raw
    (fun x y h => MetricGluing.point_eq_of_glue _ ((L.contourGraftClosedSeams_relation S x y).mp h))
    (fun x y h => MetricGluing.point_eq_of_glue _ ((L.contourGraftClosedSeams_relation S x y).mpr h))).trans
      (L.contourGraftCellIsometry S)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
