module

public import Unfoldings.Roof.CompatibleContourInteriorExcision
public import Unfoldings.Metric.InternalFamilyBalls
public import Unfoldings.Metric.CenteredBallRestriction
public import Unfoldings.Metric.PolygonalConvexChart
public import Unfoldings.Metric.CenteredBallChartRestriction

/-! Actual gap interior points have whole planar metric balls, including internal cell seams. -/

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

local instance contourGapChartMeshFintype : Fintype (T).Index :=
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

local instance contourGapChartWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Internally glued original cells retain the exact intrinsic metric of each original piece. -/
def compatibleContourInternalCoordinates (i) :
    MetricGluing.Realization (fun j => Cells i j) (Internal i).relation ≃ᵢ Pieces i :=
  (MetricGluing.changeSeamsIsometryEquiv _
    (fun x y joined => MetricGluing.point_eq_of_glue _
      ((K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W models i x y).mp joined))
    (fun x y joined => MetricGluing.point_eq_of_glue _
      ((K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W models i x y).mpr joined))).trans
    (Coordinates i)

local notation "Original" => K.compatibleContourInternalCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Every whole finite ball of the internally glued cell model is its original piece ball. -/
def compatibleContourInternalPieceBall (i) (j : Index i) (p : Cells i j) (r : ℝ) :
    Metric.eball (MetricGluing.of _ (InternalSeams).relation ⟨i, j⟩ p) (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (Original i (MetricGluing.of _ (Internal i).relation j p))
        (ENNReal.ofReal r) :=
  (MetricGluing.internalFamilyCellBall (fun i j => Cells i j) Internal i j p r).symm.trans
    (isometryEquivEBall (Original i) (MetricGluing.of _ (Internal i).relation j p)
      (ENNReal.ofReal r))

/-- Every actual gap interior point has a whole Euclidean metric ball in the full graft.
This includes points on internal gap-cell seams; no cell-interior assumption is used. -/
theorem compatibleContourGraft_gap_interior_chart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (event : Event) (j : Index (some event)) (p : Cells (some event) j)
    (interior_point : Complex.orthonormalBasisOneI.repr.symm p.val ∈
      interior (models event).region) :
    HasMetricBallChart Plane
      (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models
        (MetricGluing.of _ (Seams).relation ⟨some event, j⟩ p)) := by
  let a : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)) :=
    ⟨⟨some event, j⟩, p⟩
  let x := Original (some event) (MetricGluing.of _ (Internal (some event)).relation j p)
  have position : x.val = Complex.orthonormalBasisOneI.repr.symm p.val := rfl
  obtain ⟨C⟩ := K.compatibleContourGapInterior_forgetChart compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry event j p
    interior_point
  obtain ⟨ε, εpos, contained⟩ := Metric.isOpen_iff.mp isOpen_interior x.val
    (position.symm ▸ interior_point)
  let r := min C.radius ε
  have rpos : 0 < r := lt_min C.positive εpos
  have center : (C.chart ⟨MetricGluing.point _ (InternalSeams).relation a,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩).val =
      MetricGluing.point _ (Seams).relation a := C.agrees _
  let cut := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr C.positive)
    (ENNReal.ofReal_le_ofReal (min_le_left C.radius ε)) C.chart center
  let piece := K.compatibleContourInternalPieceBall compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models (some event) j p r
  have local_eq : ∀ z, dist z x.val < r → (z ∈ (models event).region ↔ z ∈ (Set.univ : Set ℂ)) := by
    intro z near
    exact ⟨fun _ => Set.mem_univ _, fun _ => interior_subset
      (contained (near.trans_le (min_le_right C.radius ε)))⟩
  obtain ⟨B, _⟩ := PolygonalPoint.exists_local_convex_ball_isometry x
    (⟨x.val, Set.mem_univ _⟩ : (Set.univ : Set ℂ)) rfl rpos convex_univ local_eq
  let ambient : Metric.ball (⟨x.val, Set.mem_univ _⟩ : (Set.univ : Set ℂ)) r ≃ᵢ
      Metric.ball x.val r := {
    toFun := fun z => ⟨z.val.val, z.property⟩
    invFun := fun z => ⟨⟨z.val, Set.mem_univ _⟩, z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    isometry_toFun := fun _ _ => rfl }
  let plane := (metricBallEBallEquiv x.val r).trans
    ((isometryEquivEBall Complex.orthonormalBasisOneI.repr.toIsometryEquiv x.val
      (ENNReal.ofReal r)).trans
      (metricBallEBallEquiv (Complex.orthonormalBasisOneI.repr x.val) r).symm)
  have regular : HasMetricBallChart Plane (MetricGluing.point _ (Seams).relation a) :=
    ⟨r, rpos, Complex.orthonormalBasisOneI.repr x.val,
      ⟨((cut.symm.trans piece).trans B).trans (ambient.trans plane)⟩⟩
  exact regular.isometryEquiv
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)

/-- Every original intrinsic gap interior point has a whole planar ball in the actual graft,
independently of any choice of original cell representative. -/
theorem compatibleContourGraft_gap_point_interior_chart
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (event : Event) (x : PolygonalPoint (models event).region)
    (interior_point : x.val ∈ interior (models event).region) :
    HasMetricBallChart Plane (MetricGluing.of Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap)) (some event) x) := by
  obtain ⟨y, at_x⟩ := (models event).planarCellIsometry.surjective x
  obtain ⟨⟨j, p⟩, equal⟩ := MetricGluing.point_surjective (fun j => (models event).planarCells j)
    (MetricGluing.distinctCoincident (models event).planarCells) y
  have represented : (models event).planarCellIsometry
      (MetricGluing.of _ (MetricGluing.distinctCoincident (models event).planarCells) j p) = x :=
    (congrArg (models event).planarCellIsometry equal).trans at_x
  have position : Complex.orthonormalBasisOneI.repr.symm p.val = x.val :=
    congrArg PolygonalPoint.val represented
  have regular := K.compatibleContourGraft_gap_interior_chart compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models geometry event j p
    (position.symm ▸ interior_point)
  have center : K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models
      (MetricGluing.of _ (Seams).relation ⟨some event, j⟩ p) =
      MetricGluing.of Pieces
        (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
          (MetricGluing.bankStackRight Pieces Stack Base Gap)) (some event) x :=
    (K.compatibleContourClosedSeamIsometry_point compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models ⟨some event, j⟩ p).trans
      (congrArg (MetricGluing.of Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap)) (some event)) represented)
  exact center ▸ regular

end Unfoldings.ConvexRoof
