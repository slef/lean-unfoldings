module

public import Unfoldings.Roof.CompatibleContourLabels
public import Unfoldings.Metric.ClosedSeamsTopology
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! Exact seam classes and quotient topology for the actual whole contour graft. -/

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

local instance contourFiniteClassMeshFintype : Fintype (T).Index :=
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

local instance contourFiniteClassWholeFintype : Fintype W.Index := W.finiteIndex

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

/-- Every internal seam and every actual finite/infinite attachment preserves its original label. -/
theorem compatibleContourCellLabel_seam
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x y : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (joined : Glue x y) : CellLabel x = CellLabel y := by
  cases joined with
  | «inside» i a b seam =>
    exact congrArg (fun p => PieceLabel i (Coordinates i p))
      (MetricGluing.point_eq_of_glue (fun j => Cells i j) seam)
  | between _ _ seam =>
    exact MetricGluing.bankStackSeams_label Pieces Stack Base Gap PointLabel BankLabel
      (K.compatibleContourBaseMark_label compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts W models)
      (fun bank event member side t => K.compatibleContourGapMark_label compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts W models bank
          event (geometry event) member side t) _ _ seam

/-- Actual labels have finite fibers in each original cell. Roof cells are physically
injective; gap frontiers use the derived finite-fiber maps and interior points keep their tags. -/
theorem finite_compatibleContourCellLabel_fiber
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (ij : Σ i, Index i) (label : LabelType) :
    {p : Cells ij.1 ij.2 | CellLabel ⟨ij, p⟩ = label}.Finite := by
  obtain ⟨i, j⟩ := ij
  cases i with
  | none =>
    have injection : Function.Injective (fun p : Cells none j => CellLabel ⟨⟨none, j⟩, p⟩) := by
      intro p q same
      have physical : (W.partition.cellIsometryEquiv j p).val =
          (W.partition.cellIsometryEquiv j q).val := Sum.inl.inj same
      exact (W.partition.cellIsometryEquiv j).injective (Subtype.ext physical)
    exact (show {p : Cells none j | CellLabel ⟨⟨none, j⟩, p⟩ = label}.Subsingleton from
      fun _ first _ last => injection (first.trans last.symm)).finite
  | some event =>
    have finite := MetricGluing.finite_partialLabel_fiber (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event
      (K.finite_compatibleContourGapFrontierMap_fiber compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts models event (geometry event)) label
    have injection : Function.Injective (fun p : (models event).planarCells j =>
        Complex.orthonormalBasisOneI.repr.symm p.val) := by
      intro p q same
      exact Subtype.ext (Complex.orthonormalBasisOneI.repr.symm.injective same)
    exact finite.preimage injection.injOn

/-- The actual full graft has finite seam classes, derived from its original bank geometry. -/
theorem compatibleContourCellGlue_finite_classes
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (a : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (ij : Σ i, Index i) :
    (MetricGluing.classIn (MetricGluing.NestedCell (fun i j => Cells i j)) Glue a ij).Finite :=
  MetricGluing.finite_classIn_of_finite_label_fibers Glue CellLabel
    (K.compatibleContourCellLabel_seam compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry)
    (K.finite_compatibleContourCellLabel_fiber compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry) a ij

/-- The closed-domain presentation retains these derived finite actual seam classes. -/
theorem compatibleContourClosedSeams_finite_classes
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (a : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j)))
    (ij : Σ i, Index i) :
    (MetricGluing.classIn (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation a
      ij).Finite :=
  MetricGluing.finite_classIn_of_finite_label_fibers (Seams).relation CellLabel
    (fun x y joined => K.compatibleContourCellLabel_seam compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry x y
      ((K.compatibleContourClosedSeams_relation compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W models x y).mp joined))
    (K.finite_compatibleContourCellLabel_fiber compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry) a ij

/-- No extra zero-distance identifications occur in the actual whole graft. -/
theorem compatibleContourClosedSeams_exact
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event])) :
    MetricGluing.Exact (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation :=
  (Seams).exact_of_finite_classes
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry)

/-- The actual original seam quotient has precisely the whole graft's route-metric topology.
Finite classes are proved above, rather than supplied as a topological certificate. -/
def compatibleContourGraftSeamHomeomorph
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event])) :
    MetricGluing.SeamQuotient (MetricGluing.NestedCell (fun i j => Cells i j)) (Seams).relation ≃ₜ
      K.compatibleContourGraft compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W models :=
  ((Seams).seamHomeomorph
    (K.compatibleContourClosedSeams_finite_classes compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry)).trans
    (K.compatibleContourClosedSeamIsometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models).toHomeomorph

/-- The topological identification preserves every original cell representative. -/
theorem compatibleContourGraftSeamHomeomorph_point
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event]))
    (x : MetricGluing.Total (MetricGluing.NestedCell (fun i j => Cells i j))) :
    K.compatibleContourGraftSeamHomeomorph compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry
      (MetricGluing.seamPoint _ (Seams).relation x) =
    MetricGluing.point Pieces
      (MetricGluing.bankSeams (MetricGluing.bankStackLeft Pieces Stack Base Gap)
        (MetricGluing.bankStackRight Pieces Stack Base Gap))
      (MetricGluing.mappedNestedPoint Cells Inner Coordinates x) := rfl

/-- Original convex cells and the derived actual quotient topology give local path connectivity. -/
theorem compatibleContourGraft_locallyPathConnectedSpace
    (geometry : ∀ event : Event,
      OrientedBankGap (BankAt[contour,starts,event]) (OpenedAt[contour,starts,event])) :
    LocallyPathConnectedSpace
      (K.compatibleContourGraft compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W models) := by
  let cell_lpc (ij : Σ i, Index i) : LocallyPathConnectedSpace (Cells ij.1 ij.2) :=
    (K.compatibleContourCells_geometry compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models ij.1 ij.2).2.1.locallyPathConnectedSpace
  exact (K.compatibleContourGraftSeamHomeomorph compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W models
      geometry).isQuotientMap.locallyPathConnectedSpace

end Unfoldings.ConvexRoof
