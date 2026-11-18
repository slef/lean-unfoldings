module

public import Unfoldings.Roof.CompatibleContourGraft
public import Unfoldings.Geometry.BankGapPlanarCells
public import Unfoldings.Metric.MappedBankGraft

/-! One finite planar-cell gluing retains the exact complete actual roof-plus-gap metric. -/

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

local instance contourGraftCellMeshFintype : Fintype (T).Index :=
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

local instance contourGraftCellWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Keep every actual original roof cell and every canonical gap cell as separate named pieces. -/
abbrev compatibleContourCellIndex :
    Option ((T).pairedComplex.PositiveContourSource (Fcut).selection contour) → Type
  | none => W.Index
  | some event => (models event).Cell

local notation "Index" => K.compatibleContourCellIndex compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

instance compatibleContourCellFintype (i) : Fintype (Index i) := by
  cases i
  · exact W.finiteIndex
  · exact BankGapModel.cellFintype _

/-- All cells now use common real-plane coordinates, retaining their original rigid metric. -/
def compatibleContourCells : ∀ i, Index i → Set Plane
  | none => W.partition.planarCell
  | some event => (models event).planarCells

local notation "Cells" => K.compatibleContourCells compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- Original internal piece seams omit identity seams and retain every original cut side. -/
def compatibleContourCellInner : ∀ i, MetricGluing.Total (fun j => Cells i j) →
    MetricGluing.Total (fun j => Cells i j) → Prop
  | none => W.partition.cutGlue R.carrier
  | some event => MetricGluing.distinctCoincident (models event).planarCells

local notation "Inner" => K.compatibleContourCellInner compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W models

/-- Each cell gluing recovers its literal actual intrinsic roof or gap piece. -/
def compatibleContourCellCoordinates : ∀ i,
    MetricGluing.Realization (fun j => Cells i j) (Inner i) ≃ᵢ Pieces i
  | none => IsometryEquiv.refl _
  | some event => (models event).planarCellIsometry

local notation "Coordinates" => K.compatibleContourCellCoordinates compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap

/-- The original cell seams and all literal finite/infinite bank attachments in one relation. -/
abbrev compatibleContourCellGlue :=
  MetricGluing.mappedBankGraftCells Cells Inner Coordinates Left Right

/-- This single finite planar-cell model has exactly the complete actual graft's metric. -/
def compatibleContourGraftCellIsometry :
    MetricGluing.Realization (MetricGluing.NestedCell (fun i j => Cells i j))
      (K.compatibleContourCellGlue compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models) ≃ᵢ
      K.compatibleContourGraft compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W models :=
  MetricGluing.mappedBankGraftIsometry Cells Inner Coordinates Left Right

/-- All actual graft cells are closed, convex and full dimensional; unbounded cells are retained. -/
theorem compatibleContourCells_geometry (i) (j : Index i) :
    IsClosed (Cells i j) ∧ Convex ℝ (Cells i j) ∧ (interior (Cells i j)).Nonempty := by
  cases i with
  | none => exact ⟨W.partition.isClosed_planarCell j, W.partition.convex_planarCell j,
      W.partition.planarCell_interior_nonempty j⟩
  | some event => exact ⟨(models event).planarCells_closed j,
      (models event).planarCells_convex j, (models event).planarCells_full j⟩

/-- Internal piece seams are all on actual original cell boundaries. -/
theorem compatibleContourCellInner_boundary (i) (j : Index i) (p : Cells i j)
    (seam : p ∈ MetricGluing.seamSupport (fun j => Cells i j) (Inner i) j) :
    p.val ∉ interior (Cells i j) := by
  cases i with
  | none => exact W.partition.cut_seamSupport_boundary R.carrier j p seam
  | some event => exact (models event).planarCells_seam_boundary j p seam

end Unfoldings.ConvexRoof
