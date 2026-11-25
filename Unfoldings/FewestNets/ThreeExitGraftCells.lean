module

public import Unfoldings.FewestNets.ThreeExitContourGraft
public import Unfoldings.Geometry.BankGapClosedEmbeddings
public import Unfoldings.Geometry.SpatialEnvelopeCutCellIsometry
public import Unfoldings.Metric.MappedBankGraft

/-! The complete ordered graft has one finite planar-cell presentation. -/

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

local instance graftCellsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

/-- Original roof cells and source-gap cells retain separate names. -/
abbrev contourGraftCellIndex : Option Event → Type
  | none => L.whole.Index
  | some e => Model[e].Cell

local notation "Index" => contourGraftCellIndex L S

instance contourGraftCellIndexFintype (i : Option Event) : Fintype (Index i) := by
  cases i with
  | none => exact L.whole.finiteIndex
  | some e => exact BankGapModel.cellFintype Model[e]

/-- All cells use the same real-plane coordinate space. -/
def contourGraftCells : ∀ i, Index i → Set Plane
  | none => L.whole.partition.planarCell
  | some e => Model[e].planarCells

local notation "Cells" => contourGraftCells L S

/-- Internal piece seams preserve the original graph cut or the rigid gap cell geometry. -/
def contourGraftCellInner : ∀ i, MetricGluing.Total (fun j => Cells i j) →
    MetricGluing.Total (fun j => Cells i j) → Prop
  | none => L.whole.partition.cutGlue R.wholeCarrier
  | some e => MetricGluing.distinctCoincident Model[e].planarCells

local notation "Inner" => contourGraftCellInner L S

/-- The cells of an individual piece give precisely its intrinsic cut metric. -/
def contourGraftCellCoordinates : ∀ i,
    MetricGluing.Realization (fun j => Cells i j) (Inner i) ≃ᵢ Pieces i
  | none => IsometryEquiv.refl _
  | some e => Model[e].planarCellIsometry

local notation "Coordinates" => contourGraftCellCoordinates L S
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)

abbrev contourGraftCellGlue := MetricGluing.mappedBankGraftCells Cells Inner Coordinates Left Right

/-- Flattening the hierarchy of polygonal pieces preserves all distances of the ordered graft. -/
def contourGraftCellIsometry :
    MetricGluing.Realization Raw (L.contourGraftCellGlue S) ≃ᵢ L.contourGraft S :=
  MetricGluing.mappedBankGraftIsometry Cells Inner Coordinates Left Right

theorem contourGraftCell_geometry (i : Option Event) (j : Index i) :
    IsClosed (Cells i j) ∧ Convex ℝ (Cells i j) ∧ (interior (Cells i j)).Nonempty := by
  cases i with
  | none => exact ⟨L.whole.partition.isClosed_planarCell j, L.whole.partition.convex_planarCell j,
      L.whole.partition.planarCell_interior_nonempty j⟩
  | some e => exact ⟨Model[e].planarCells_closed j, Model[e].planarCells_convex j,
      Model[e].planarCells_full j⟩

/-- In each planar cell of the graft the spatial collapse is already a proper map. -/
theorem isProperMap_contourGraftCellCollapse (ij : Σ i, Index i) :
    IsProperMap (fun p : Raw ij =>
      let y := MetricGluing.mappedNestedPoint Cells Inner Coordinates ⟨ij, p⟩
      L.contourGraftPieceCollapse S y.1 y.2) := by
  obtain ⟨i, j⟩ := ij
  cases i with
  | none =>
    let : CompleteSpace (Raw ⟨none, j⟩) :=
      (L.whole.partition.isClosed_planarCell j).isComplete.completeSpace_coe
    have isometric : Isometry (fun p : Raw ⟨none, j⟩ =>
        (L.whole.partition.restoreCut R.wholeCarrier (MetricGluing.of _ _ j p)).val) := by
      intro x y
      exact (congrArg₂ (fun u v : Space => edist u v)
        (L.whole.partition.restoreCut_of R.wholeCarrier j x)
        (L.whole.partition.restoreCut_of R.wholeCarrier j y)).trans
          ((M.plane (L.whole.partition.support j)).place.isometry.edist_eq x.val y.val)
    exact isometric.isClosedEmbedding.isProperMap
  | some e =>
    let path := (Fcut).contourSourceSpatialRay S.contour S.starts e
    have dir_ne : path.direction ≠ 0 :=
      (Fcut).contourSourceSpatialRay_direction_ne_zero S.contour S.starts e
    exact ((path.isClosed_carrier dir_ne).isClosedEmbedding_subtypeVal.isProperMap.comp
      (R.isProperMap_contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e))).comp
      (Model[e].planarCell_intrinsic_isClosedEmbedding j).isProperMap

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
