module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraft
public import Unfoldings.Roof.CompatibleContourBankEmbeddings
public import Unfoldings.Roof.CompatibleContourMarkCarrier
public import Unfoldings.Metric.ClosedBankStackCells
public import Unfoldings.Metric.BankStackCellBoundary
public import Unfoldings.Metric.BoundaryCellInteriorChart
public import Unfoldings.Metric.ClosedCoincidentSeams
public import Unfoldings.Geometry.SpatialEnvelopeCutCellIsometry

/-! A single finite closed-cell presentation of the source-only contour graft. -/

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

local instance sourceOnlyGraftCellsIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyGraftCellsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

/-- Keep every actual original roof cell and every source-only gap cell as separate named pieces. -/
abbrev compatibleContourSourceOnlyCellIndex :
    Option ((T).pairedComplex.PositiveContourSource (Fcut).selection contour) → Type
  | none => W.Index
  | some event => (models event).Cell

local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M
  positive inner_disk beta acute contour starts W models

instance compatibleContourSourceOnlyCellFintype (i) : Fintype (Index i) := by
  cases i
  · exact W.finiteIndex
  · exact BankGapModel.cellFintype _

/-- All cells now use common real-plane coordinates, retaining their original rigid metric. -/
def compatibleContourSourceOnlyCells : ∀ i, Index i → Set Plane
  | none => W.partition.planarCell
  | some event => (models event).planarCells

local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary
  level higher M
  positive inner_disk beta acute contour starts W models

/-- Original internal piece seams omit identity seams and retain every original cut side. -/
def compatibleContourSourceOnlyCellInner : ∀ i, MetricGluing.Total (fun j => Cells i j) →
    MetricGluing.Total (fun j => Cells i j) → Prop
  | none => W.partition.cutGlue R.carrier
  | some event => MetricGluing.distinctCoincident (models event).planarCells

local notation "Inner" => K.compatibleContourSourceOnlyCellInner compact nonempty R no_boundary
  level higher M
  positive inner_disk beta acute contour starts W models

/-- Each cell gluing recovers its literal actual intrinsic roof or gap piece. -/
def compatibleContourSourceOnlyCellCoordinates : ∀ i,
    MetricGluing.Realization (fun j => Cells i j) (Inner i) ≃ᵢ Pieces i
  | none => IsometryEquiv.refl _
  | some event => (models event).planarCellIsometry

local notation "Coordinates" => K.compatibleContourSourceOnlyCellCoordinates compact nonempty R
  no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap

/-- The original cell seams and all literal finite/infinite bank attachments in one relation. -/
abbrev compatibleContourSourceOnlyCellGlue :=
  MetricGluing.mappedBankGraftCells Cells Inner Coordinates Left Right

/-- This single finite planar-cell model has exactly the complete actual graft's metric. -/
def compatibleContourSourceOnlyGraftCellIsometry :
    MetricGluing.Realization (MetricGluing.NestedCell (fun i j => Cells i j))
      (K.compatibleContourSourceOnlyCellGlue compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models) ≃ᵢ
      K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary level higher M positive
        inner_disk
        beta acute contour starts W models :=
  MetricGluing.mappedBankGraftIsometry Cells Inner Coordinates Left Right

/-- All actual graft cells are closed, convex and full dimensional; unbounded cells are retained. -/
theorem compatibleContourSourceOnlyCells_geometry (i) (j : Index i) :
    IsClosed (Cells i j) ∧ Convex ℝ (Cells i j) ∧ (interior (Cells i j)).Nonempty := by
  cases i with
  | none => exact ⟨W.partition.isClosed_planarCell j, W.partition.convex_planarCell j,
      W.partition.planarCell_interior_nonempty j⟩
  | some event => exact ⟨(models event).planarCells_closed j,
      (models event).planarCells_convex j, (models event).planarCells_full j⟩

/-- Internal piece seams are all on actual original cell boundaries. -/
theorem compatibleContourSourceOnlyCellInner_boundary (i) (j : Index i) (p : Cells i j)
    (seam : p ∈ MetricGluing.seamSupport (fun j => Cells i j) (Inner i) j) :
    p.val ∉ interior (Cells i j) := by
  cases i with
  | none => exact W.partition.cut_seamSupport_boundary R.carrier j p seam
  | some event => exact (models event).planarCells_seam_boundary j p seam

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e

/-- Source-only gaps retain genuine edges on both banks. -/
theorem compatibleContourSourceOnlyBank_edge_ne_zero (event : Event) (side : Bool)
    (i : Fin (LengthAt[event] + 1)) : ((models event).bank side).chain.edge i ≠ 0 := by
  have first := K.compatibleContourSourceBank_edge_length compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts event i
  have genuine : (BankAt[event]).chain.edge i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [first]
    exact ((D).boundaryBankLength_pos _).ne'
  cases side
  · exact genuine
  · change (MovedAt[event]).chain.edge i ≠ 0
    unfold compatibleContourSourceOnlyBank
    rw [PolygonalRay.rotateSuffix_zero_edge]
    simpa only [map_zero] using (complexRotation _).injective.ne genuine

/-- The infinite bank continues its exact final finite edge on either side. -/
theorem compatibleContourSourceOnlyBank_direction_eq_last (event : Event) (side : Bool) :
    ((models event).bank side).direction =
      ((models event).bank side).chain.edge (Fin.last LengthAt[event]) := by
  cases side
  · rfl
  · change (MovedAt[event]).direction = (MovedAt[event]).chain.edge _
    unfold compatibleContourSourceOnlyBank
    rw [PolygonalRay.rotateSuffix_zero_edge]
    rfl

/-- The two literal roof bank maps are closed embeddings on their full domains. -/
theorem compatibleContourSourceOnlyBaseMark_isClosedEmbedding (bank : Attachment) (side : Bool) :
    Topology.IsClosedEmbedding (Base bank side) := by
  cases bank with
  | inl v =>
    exact Dilation.isClosedEmbedding
      (K.compatibleContourParentDilation compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W v.val v.property side)
  | inr e =>
    exact Dilation.isClosedEmbedding
      (K.compatibleContourTailDilation compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W e side)

/-- Both sides of the original roof bank use the same intrinsic parameter metric. -/
theorem compatibleContourSourceOnlyBaseMark_metric (bank : Attachment) (side : Bool)
    (s t : ParamAt bank) :
    edist (Base bank side s) (Base bank side t) =
      edist (Base bank false s) (Base bank false t) := by
  cases bank with
  | inl v =>
    cases side
    · rfl
    · exact (K.edist_compatibleContourParentMark_sides compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W v.val v.property s t).symm
  | inr edge =>
    exact (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side s t).trans
      (K.edist_compatibleContourTerminalMark_eq_length compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W edge false s t).symm

/-- Each attached source-only bank is a closed embedding. -/
theorem compatibleContourSourceOnlyGapMark_isClosedEmbedding (bank : Attachment) (event : Event)
    (member : event ∈ Stack bank) (side : Bool) :
    Topology.IsClosedEmbedding (Gap bank event member side) := by
  have edge := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models event (!side)
  cases bank with
  | inl v => exact (models event).edgePoint_isClosedEmbedding (!side) _ (edge _)
  | inr r =>
    apply (models event).tailPoint_isClosedEmbedding
    rw [K.compatibleContourSourceOnlyBank_direction_eq_last compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models event (!side)]
    exact edge _

/-- Each actual planar cell embeds isometrically into its intrinsic piece. -/
theorem compatibleContourSourceOnlyCellCoordinates_isometry (i) (j : Index i) :
    Isometry (fun p : Cells i j => Coordinates i
      (MetricGluing.of (fun j => Cells i j) (Inner i) j p)) := by
  cases i with
  | none => exact W.partition.cut_cell_isometry R.carrier j
  | some event => exact (models event).planarCell_intrinsic_isometry j

/-- Use the roof cut seams and the actual internal seams of each source-only gap. -/
def compatibleContourSourceOnlyInternalSeams : ∀ i,
    MetricGluing.ClosedSeams (fun j => Cells i j)
  | none => MetricGluing.ClosedSeams.reparametrize
      (W.partition.cutPhysicalSeams R.carrier).offDiagonal.closedSeams
      W.partition.cellIsometryEquiv
  | some event => MetricGluing.distinctCoincidentClosedSeams (models event).planarCells
      (models event).planarCells_closed

local notation "Geometry" => K.compatibleContourSourceOnlyCells_geometry compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models
local notation "Internal" => K.compatibleContourSourceOnlyInternalSeams compact nonempty R
  no_boundary level higher
  M positive inner_disk beta acute contour starts W models

/-- A finite family of literal isometric closed seams presents the actual source-only graft. -/
def compatibleContourSourceOnlyClosedSeams :
    MetricGluing.ClosedSeams (MetricGluing.NestedCell (fun i j => Cells i j)) :=
  MetricGluing.bankStackClosedSeams Pieces Stack Base Gap Cells Inner Coordinates
    (K.compatibleContourSourceOnlyCellCoordinates_isometry compact nonempty R no_boundary
      level higher M positive inner_disk
      beta acute contour starts W models) (fun i j => (Geometry i j).1)
    (K.compatibleContourSourceOnlyBaseMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk
      beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk
      beta acute contour starts models)
    (K.compatibleContourSourceOnlyBaseMark_metric compact nonempty R no_boundary
      level higher M positive inner_disk
      beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_metric compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models) Internal

local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "GraftGlue" => K.compatibleContourSourceOnlyCellGlue compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Closed domains retain exactly the original internal and bank seam relations. -/
theorem compatibleContourSourceOnlyClosedSeams_relation (x y : MetricGluing.Total Raw) :
    (Seams).relation x y ↔ GraftGlue x y := by
  unfold compatibleContourSourceOnlyClosedSeams
  apply MetricGluing.bankStackClosedSeams_relation
  intro i x y
  cases i with
  | none => exact MetricGluing.ClosedSeams.reparametrize_relation _ _ x y
  | some event =>
    exact MetricGluing.distinctCoincidentClosedSeams_relation
      (models event).planarCells (models event).planarCells_closed x y

/-- The closed-seam construction preserves the route metric of the actual source-only graft. -/
def compatibleContourSourceOnlyClosedSeamsIsometry :
    MetricGluing.Realization (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation ≃ᵢ
      K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models := by
  let exactRel := K.compatibleContourSourceOnlyClosedSeams_relation compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  exact (MetricGluing.changeSeamsIsometryEquiv Raw
    (fun x y h => MetricGluing.point_eq_of_glue _ ((exactRel x y).mp h))
    (fun x y h => MetricGluing.point_eq_of_glue _ ((exactRel x y).mpr h))).trans
      (K.compatibleContourSourceOnlyGraftCellIsometry compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models)

/-- Every seam of the source-only graft identifies only original planar cell boundaries. -/
theorem compatibleContourSourceOnlyClosedSeams_boundary :
    ∀ (ij : Σ i, Index i) (p : Cells ij.1 ij.2),
      p ∈ MetricGluing.seamSupport Raw (Seams).relation ij →
        p.val ∉ interior (Cells ij.1 ij.2) := by
  have old : ∀ (ij : Σ i, Index i) (p : Cells ij.1 ij.2),
      p ∈ MetricGluing.seamSupport Raw GraftGlue ij → p.val ∉ interior (Cells ij.1 ij.2) := by
    apply MetricGluing.bankStackCells_boundary Cells Inner Coordinates Stack Base Gap
    · exact K.compatibleContourSourceOnlyCellInner_boundary compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models
    · intro bank side t ij p named
      apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
      intro j q equal
      cases bank with
      | inl vertex =>
        exact W.cell_boundary_of_restore_mem j q _ equal
          (K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
            positive inner_disk beta acute contour starts W vertex.val vertex.property side t)
      | inr edge =>
        exact W.cell_boundary_of_restore_mem j q _ equal
          (K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
            positive inner_disk beta acute contour starts W edge side t)
    · intro bank event member side t ij p named
      apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
      intro j q equal
      cases bank with
      | inl vertex => exact (models event).planarCell_edge_boundary (!side) _ t j q equal
      | inr edge => exact (models event).planarCell_tail_boundary (!side) t j q equal
  have relation := K.compatibleContourSourceOnlyClosedSeams_relation compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  intro ij p supports
  apply old ij p
  rcases supports with ⟨y, same⟩ | ⟨y, same⟩
  · exact Or.inl ⟨y, (relation _ _).mp same⟩
  · exact Or.inr ⟨y, (relation _ _).mp same⟩

/-- Every original cell interior in the revised graft has a whole planar metric ball. -/
theorem compatibleContourSourceOnlyGraft_cell_interior_chart (ij : Σ i, Index i)
    (p : Cells ij.1 ij.2) (interior_point : p.val ∈ interior (Cells ij.1 ij.2)) :
    HasMetricBallChart Plane
      (K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W models
          (MetricGluing.of Raw (Seams).relation ij p)) := by
  have chart := MetricGluing.hasMetricBallChart_of_cell_interior
    (fun ij : Σ i, Index i => Cells ij.1 ij.2) (Seams).relation
    (K.compatibleContourSourceOnlyClosedSeams_boundary compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models) ij p interior_point
  exact chart.isometryEquiv (K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W models)

end Unfoldings.ConvexRoof
