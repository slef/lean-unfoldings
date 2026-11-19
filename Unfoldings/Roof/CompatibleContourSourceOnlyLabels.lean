module

public import Unfoldings.Roof.CompatibleContourSourceOnlyGraftCells
public import Unfoldings.Roof.CompatibleContourPhysicalTails
public import Unfoldings.Metric.BankStackLabels
public import Unfoldings.Metric.FiniteLabelClasses
public import Unfoldings.Metric.FinitePartialLabels
public import Unfoldings.Metric.ClosedSeamsTopology
public import Mathlib.Analysis.Convex.Topology

/-! The source-only bank seams preserve exact original labels with finite fibers. -/

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

local instance sourceOnlyLabelsIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlyLabelsWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "LengthAt[" e "]" => TriangleComplex.positiveContourBankLength D Selection contour e
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "IndexAt[" v "," h "," e "," member "]" =>
  TriangleComplex.contourGapBankIndex D Selection contour v h e
    (Iff.mpr (TriangleComplex.mem_contourEdgeGapStack D Selection contour v e)
      (Iff.mp (TriangleComplex.mem_contourSavedGapStack D Selection contour v e) member))

/-- Collapse either literal source-only bank to the original physical rootward path. -/
def compatibleContourSourceOnlyFrontierMap (event : Event) :
    frontier (models event).region → (SpatialAt[event]).carrier :=
  (models event).frontierMap (SpatialAt[event])

local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e

/-- The map uses the original arclength parameter at every finite or infinite point. -/
theorem compatibleContourSourceOnlyFrontierMap_address (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event]) (side : Bool)
    (addr : PolygonalRay.Address (LengthAt[event] + 1)) :
    FoldAt[event] ((models event).addressFrontier side addr) =
      ⟨(SpatialAt[event]).addressPoint addr, (SpatialAt[event]).addressPoint_mem addr⟩ := by
  have genuine := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts models event
  exact (models event).frontierMap_address g.first_outward (genuine false) g.first_nonzero
    g.second_outward (genuine true) g.second_nonzero g.common (SpatialAt[event]) side addr

/-- Each original physical point has only finitely many boundary representatives per gap. -/
theorem finite_compatibleContourSourceOnlyFrontierMap_fiber (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event]) (p : Space) :
    {z : frontier (models event).region | (FoldAt[event] z).val = p}.Finite := by
  classical
  have genuine := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts models event
  by_cases member : p ∈ (SpatialAt[event]).carrier
  · have finite := (models event).finite_frontierMap_fiber g.first_outward (genuine false)
      g.first_nonzero g.second_outward (genuine true) g.second_nonzero g.common (SpatialAt[event])
      (K.compatibleContourPhysicalBank_edge_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts event)
      (K.compatibleContourPhysicalBank_direction_ne_zero compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts event) ⟨p, member⟩
    exact finite.subset (fun _ equal => Subtype.ext equal)
  · apply Set.finite_empty.subset
    intro z equal
    exact (member (equal ▸ (FoldAt[event] z).property)).elim

local notation "Label" => Space ⊕ (Event × ℂ)

/-- Points on bank seams use their original physical label. Every gap interior
retains its own piece tag and coordinate. -/
def compatibleContourSourceOnlyPieceLabel : ∀ i, Pieces i → Label
  | none => fun p => .inl (W.partition.restoreCut R.carrier p).val
  | some event => fun p => MetricGluing.partialLabel (frontier (models event).region)
    (fun z => (FoldAt[event] z).val) event p.val

local notation "LabelAt" => K.compatibleContourSourceOnlyPieceLabel compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models
local notation "BankLabel" => fun (bank : Attachment) (t : ParamAt bank) =>
  LabelAt none (Base bank false t)

/-- Both roof sides carry the same original physical label. -/
theorem compatibleContourSourceOnlyBaseMark_label (bank : Attachment) (side : Bool)
    (t : ParamAt bank) : LabelAt none (Base bank side t) = BankLabel bank t := by
  apply congrArg Sum.inl
  cases bank with
  | inl v =>
    exact (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W v.val v.property side t).trans
      (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts W v.val v.property false t).symm
  | inr edge =>
    exact (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W edge side t).trans
      (K.restore_compatibleContourTerminalMark compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W edge false t).symm

/-- The complemented side still carries the physical label of its named attachment. -/
theorem compatibleContourSourceOnlyGapMark_label (bank : Attachment) (event : Event)
    (g : OrientedBankGap BankAt[event] MovedAt[event]) (member : event ∈ Stack bank)
    (side : Bool) (t : ParamAt bank) :
    LabelAt (some event) (Gap bank event member side t) = BankLabel bank t := by
  have fold := K.compatibleContourSourceOnlyFrontierMap_address compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models event g (!side)
  cases bank with
  | inl vertex =>
    let addr : PolygonalRay.Address (LengthAt[event] + 1) :=
      .inl (IndexAt[vertex.val,vertex.property,event,member], t)
    let b := (models event).addressFrontier (!side) addr
    have coordinate := congrArg Subtype.val (fold addr)
    exact (MetricGluing.partialLabel_of_mem (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event b.val b.property).trans
      (congrArg Sum.inl (coordinate.trans
        ((K.compatibleContourPhysicalBank_parent_point compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts vertex.val vertex.property
            event member t).trans
          (K.restore_compatibleContourParentMark_position compact nonempty R no_boundary level
            higher M positive inner_disk beta acute contour starts W vertex.val vertex.property
              false t).symm)))
  | inr edge =>
    let b := (models event).addressFrontier (!side) (.inr t)
    have coordinate := congrArg Subtype.val (fold (.inr t))
    exact (MetricGluing.partialLabel_of_mem (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event b.val b.property).trans
      (congrArg Sum.inl (coordinate.trans
        ((K.compatibleContourPhysicalBank_tail_parent compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts W edge event member t).trans
          (K.restore_compatibleContourTerminalMark_affine compact nonempty R no_boundary level
            higher M positive inner_disk beta acute contour starts W edge false t).symm)))

local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Cells" => K.compatibleContourSourceOnlyCells compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts W models
local notation "Inner" => K.compatibleContourSourceOnlyCellInner compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "Coordinates" => K.compatibleContourSourceOnlyCellCoordinates compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts W models
local notation "Raw" => MetricGluing.NestedCell (fun i j => Cells i j)
local notation "Seams" => K.compatibleContourSourceOnlyClosedSeams compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- Every raw planar cell point inherits its labelled intrinsic representative. -/
def compatibleContourSourceOnlyCellLabel (x : MetricGluing.Total Raw) : Label :=
  let y := MetricGluing.mappedNestedPoint Cells Inner Coordinates x
  LabelAt y.1 y.2

local notation "CellLabel" => K.compatibleContourSourceOnlyCellLabel compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- The exact source-only seam relation preserves physical and interior labels. -/
theorem compatibleContourSourceOnlyCellLabel_seam
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (x y : MetricGluing.Total Raw) (joined : (Seams).relation x y) :
    CellLabel x = CellLabel y := by
  have seam := (K.compatibleContourSourceOnlyClosedSeams_relation compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models x y).mp joined
  cases seam with
  | «inside» i a b same =>
    exact congrArg (fun p => LabelAt i (Coordinates i p))
      (MetricGluing.point_eq_of_glue (fun j => Cells i j) same)
  | between _ _ same =>
    exact MetricGluing.bankStackSeams_label Pieces Stack Base Gap
      (fun x => LabelAt x.1 x.2) BankLabel
      (K.compatibleContourSourceOnlyBaseMark_label compact nonempty R no_boundary level higher
        M positive inner_disk beta acute contour starts W models)
      (fun bank event member side t => K.compatibleContourSourceOnlyGapMark_label compact
        nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W
        models bank event (geometry event) member side t) _ _ same

/-- Each cell has finite fibers over the original labels. -/
theorem finite_compatibleContourSourceOnlyCellLabel_fiber
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (ij : Σ i, Index i) (label : Label) :
    {p : Cells ij.1 ij.2 | CellLabel ⟨ij, p⟩ = label}.Finite := by
  obtain ⟨i, j⟩ := ij
  cases i with
  | none =>
    have injective : Function.Injective (fun p : Cells none j =>
        CellLabel ⟨⟨none, j⟩, p⟩) := by
      intro p q same
      have physical : (W.partition.cellIsometryEquiv j p).val =
          (W.partition.cellIsometryEquiv j q).val := Sum.inl.inj same
      exact (W.partition.cellIsometryEquiv j).injective (Subtype.ext physical)
    exact (show {p : Cells none j | CellLabel ⟨⟨none, j⟩, p⟩ = label}.Subsingleton from
      fun _ first _ last => injective (first.trans last.symm)).finite
  | some event =>
    have finite := MetricGluing.finite_partialLabel_fiber (frontier (models event).region)
      (fun z => (FoldAt[event] z).val) event
      (K.finite_compatibleContourSourceOnlyFrontierMap_fiber compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models event (geometry event))
      label
    have injective : Function.Injective (fun p : (models event).planarCells j =>
        Complex.orthonormalBasisOneI.repr.symm p.val) := by
      intro p q same
      exact Subtype.ext (Complex.orthonormalBasisOneI.repr.symm.injective same)
    exact finite.preimage injective.injOn

/-- Every source-only equivalence class has finitely many representatives per original cell. -/
theorem compatibleContourSourceOnlyClosedSeams_finite_classes
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event])
    (a : MetricGluing.Total Raw) (ij : Σ i, Index i) :
    (MetricGluing.classIn Raw (Seams).relation a ij).Finite :=
  MetricGluing.finite_classIn_of_finite_label_fibers (Seams).relation CellLabel
    (K.compatibleContourSourceOnlyCellLabel_seam compact nonempty R no_boundary level higher
      M positive inner_disk beta acute contour starts W models geometry)
    (K.finite_compatibleContourSourceOnlyCellLabel_fiber compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry) a ij

/-- There are exactly the prescribed identifications in the source-only route metric. -/
theorem compatibleContourSourceOnlyClosedSeams_exact
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event]) :
    MetricGluing.Exact Raw (Seams).relation :=
  (Seams).exact_of_finite_classes
    (K.compatibleContourSourceOnlyClosedSeams_finite_classes compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry)

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

/-- The intrinsic metric has the original closed-seam quotient topology. -/
def compatibleContourSourceOnlyGraftSeamHomeomorph
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event]) :
    MetricGluing.SeamQuotient Raw (Seams).relation ≃ₜ Graft :=
  ((Seams).seamHomeomorph
    (K.compatibleContourSourceOnlyClosedSeams_finite_classes compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry)).trans
    (K.compatibleContourSourceOnlyClosedSeamsIsometry compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models).toHomeomorph

/-- Local path connectivity follows from the original convex cells and the quotient topology. -/
theorem compatibleContourSourceOnlyGraft_locallyPathConnectedSpace
    (geometry : ∀ event : Event, OrientedBankGap BankAt[event] MovedAt[event]) :
    LocallyPathConnectedSpace Graft := by
  have cell_geometry := K.compatibleContourSourceOnlyCells_geometry compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models
  let _ (ij : Σ i, Index i) : LocallyPathConnectedSpace (Cells ij.1 ij.2) :=
    (cell_geometry ij.1 ij.2).2.1.locallyPathConnectedSpace
  exact (K.compatibleContourSourceOnlyGraftSeamHomeomorph compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models
      geometry).isQuotientMap.locallyPathConnectedSpace

end Unfoldings.ConvexRoof
