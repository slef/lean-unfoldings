module

public import Unfoldings.Roof.CompatibleContourBankClosedSeams
public import Unfoldings.Metric.ClosedSeamOperations
public import Unfoldings.Metric.ClosedCoincidentSeams

/-! The entire actual graft retains a finite closed isometric seam system. -/

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
local notation "conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance contourClosedMeshFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "SourceAt[" q "," i "]" => TriangleComplex.contourOriginalVertex
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut) q i
local notation "RetainAt[" q "," i "]" => TriangleComplex.processedParentRetain
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
  (PotentialCutForest.selection Fcut)
  (TriangleComplex.contourFrontier
    (SpatialEnvelope.Triangulation.pairedComplex
      (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T))
    (PotentialCutForest.selection Fcut) q i)

local notation "ChainAt[" q "," h "," i "," hf "," n "," hn "]" =>
  K.compatibleMeshFreshSourceBankChain compact nonempty R no_boundary level higher M positive
    inner_disk beta acute q h i hf n hn

local notation "cap" => SpatialEnvelope.Triangulation.normalizedCap
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) conforming inside
local notation "RollAt[" q "," h "," i "," hf "," n "," hn "]" => TriangleComplex.boundaryChainRoll
  (SpatialEnvelope.Triangulation.pairedComplex
    (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)) ChainAt[q,h,i,hf,n,hn]

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
local notation "LengthAt[" q "," e "]" => TriangleComplex.positiveContourBankLength D Selection q e
local notation "SpanAt[" q "," e "]" => TriangleComplex.positiveContourBank_span D Selection q e
local notation "VertexAt[" q "," e "]" => TriangleComplex.positiveContourVertex D Selection q e

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

local instance contourClosedWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Map" => K.compatibleMeshWholeMap compact nonempty R no_boundary level higher M
  positive inner_disk beta acute W

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

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

/-- Original retained roof seams and all original internal gap seams have closed domains. -/
def compatibleContourInternalClosedSeams : ∀ i,
    MetricGluing.ClosedSeams (fun j => Cells i j)
  | none => MetricGluing.ClosedSeams.reparametrize
      (W.partition.cutPhysicalSeams R.carrier).offDiagonal.closedSeams
      W.partition.cellIsometryEquiv
  | some event => MetricGluing.distinctCoincidentClosedSeams (models event).planarCells
      (models event).planarCells_closed

local notation "Internal" => K.compatibleContourInternalClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Constructing closed internal domains preserves every original seam, including cut sides. -/
theorem compatibleContourInternalClosedSeams_relation (i)
    (x y : MetricGluing.Total (fun j => Cells i j)) :
    (Internal i).relation x y ↔ Inner i x y := by
  cases i with
  | none => exact MetricGluing.ClosedSeams.reparametrize_relation _ _ x y
  | some event =>
    exact MetricGluing.distinctCoincidentClosedSeams_relation
      (models event).planarCells (models event).planarCells_closed x y

/-- The full original graft: internal piece seams together with every finite or infinite bank. -/
def compatibleContourClosedSeams :
    MetricGluing.ClosedSeams (MetricGluing.NestedCell (fun i j => Cells i j)) :=
  (MetricGluing.ClosedSeams.ofFamily (fun i j => Cells i j) Internal).sum
    (K.compatibleContourBankClosedSeams compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)

local notation "Seams" => K.compatibleContourClosedSeams compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Glue" => K.compatibleContourCellGlue compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- The finite closed-seam presentation is exactly the complete original graft relation. -/
theorem compatibleContourClosedSeams_relation
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j))) :
    (Seams).relation x y ↔ Glue x y := by
  refine (MetricGluing.ClosedSeams.sum_relation _ _ x y).trans ?_
  constructor
  · rintro (joined | joined)
    · obtain ⟨i, a, b, seam, rfl, rfl⟩ :=
        (MetricGluing.ClosedSeams.ofFamily_relation _ _ x y).mp joined
      exact MetricGluing.NestedGlue.inside (E := fun i j => Cells i j) (inner := Inner) i a b
        ((K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W models i a b).mp seam)
    · exact .between x y
        ((K.compatibleContourBankClosedSeams_relation compact nonempty R no_boundary level higher
          M positive inner_disk beta acute contour starts W models x y).mp joined)
  · intro joined
    cases joined with
    | «inside» i a b seam =>
      exact Or.inl ((MetricGluing.ClosedSeams.ofFamily_relation _ _ _ _).mpr
        ⟨i, a, b, (K.compatibleContourInternalClosedSeams_relation compact nonempty R no_boundary
          level higher M positive inner_disk beta acute contour starts W models i a b).mpr seam,
          rfl, rfl⟩)
    | between _ _ seam =>
      exact Or.inr ((K.compatibleContourBankClosedSeams_relation compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts W models x y).mpr seam)

/-- The closed-seam presentation has the complete original route metric, without a
finite-class, topology or flatness hypothesis. -/
def compatibleContourClosedSeamIsometry :
    MetricGluing.Realization (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation ≃ᵢ
      K.compatibleContourGraft compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W models :=
  (MetricGluing.changeSeamsIsometryEquiv _
    (fun x y joined => MetricGluing.point_eq_of_glue _
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mp joined))
    (fun x y joined => MetricGluing.point_eq_of_glue _
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mpr joined))).trans
    (K.compatibleContourGraftCellIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models)

/-- Passing to closed seam domains keeps every original intrinsic point fixed. -/
theorem compatibleContourClosedSeamIsometry_point
    (ij : Σ i, Index i) (p : Cells ij.1 ij.2) :
    K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models
      (MetricGluing.of (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation ij p) =
    MetricGluing.point Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap))
      (MetricGluing.mappedNestedPoint Cells Inner Coordinates ⟨ij, p⟩) := rfl

end Unfoldings.ConvexRoof
