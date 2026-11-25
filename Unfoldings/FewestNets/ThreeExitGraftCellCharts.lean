module

public import Unfoldings.FewestNets.ThreeExitGraftOffCutFiber
public import Unfoldings.Geometry.SpatialEnvelopeRefinement
public import Unfoldings.Metric.BankStackCellBoundary
public import Unfoldings.Metric.BoundaryCellInteriorChart

/-! Every actual cell interior embeds with its full planar ball in the three-exit graft. -/

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

local instance graftChartsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Seams" => contourGraftClosedSeams L S

/-- The chosen alignment puts the prescribed cut on the boundaries of all original roof cells. -/
theorem wholeCell_interior_disjoint_cut (i : L.whole.Index) :
    Disjoint (interior (L.whole.partition.footprint i)) R.wholeCarrier := by
  rw [Set.disjoint_left]
  intro p inside cut
  obtain ⟨j, zero⟩ := R.wholeCarrier_covered_by_equations cut
  have border := L.whole.partition.mem_frontier_of_constraint R.wholeCutEquation
    R.wholeCutEquation_ne_zero L.whole.signs L.whole.aligned i (interior_subset inside) j zero
  exact (Set.disjoint_left.mp disjoint_interior_frontier) inside border

private theorem roofCell_boundary_of_restore_mem (j : L.whole.Index) (p : Cells none j)
    (x : L.whole.Cut) (named : Coordinates none (MetricGluing.of (fun j => Cells none j)
      (Inner none) j p) = x)
    (on_cut : Cap.horizontal (L.whole.partition.restoreCut R.wholeCarrier x).val ∈ R.wholeCarrier) :
    p.val ∉ interior (Cells none j) := by
  intro inside
  apply Set.disjoint_left.mp
    (SpatialEnvelope.WholePartition.Refinement.commonRegion_cut_disjoint_interior
      (P := L.whole.partition) R.wholeCarrier L.wholeCell_interior_disjoint_cut j) inside
  change Cap.horizontal ((M.plane (L.whole.partition.support j)).place p.val) ∈ R.wholeCarrier
  let q : L.whole.partition.planarCell j := p
  have cell_eq : MetricGluing.of (fun a => L.whole.partition.planarCell a)
      (L.whole.partition.cutGlue R.wholeCarrier) j q = x := named
  have value := (L.whole.partition.restoreCut_of R.wholeCarrier j q).symm.trans
    (congrArg (fun z => (L.whole.partition.restoreCut R.wholeCarrier z).val) cell_eq)
  exact (congrArg Cap.horizontal value).symm ▸ on_cut

private theorem contourGraftCellInner_boundary (i : Option Event) (j : Index i) (p : Cells i j)
    (seam : p ∈ MetricGluing.seamSupport (fun j => Cells i j) (Inner i) j) :
    p.val ∉ interior (Cells i j) := by
  cases i with
  | none => exact L.whole.partition.cut_seamSupport_boundary R.wholeCarrier j p seam
  | some e => exact (Model[e]).planarCells_seam_boundary j p seam

/-- No closed graft seam occupies the interior of an original cell. -/
theorem contourGraftClosedSeams_boundary (ij : Σ i, Index i) (p : Raw ij)
    (seam : p ∈ MetricGluing.seamSupport Raw (Seams).relation ij) :
    p.val ∉ interior (Cells ij.1 ij.2) := by
  have boundary (ij : Σ i, Index i) (p : Raw ij)
      (seam : p ∈ MetricGluing.seamSupport Raw (L.contourGraftCellGlue S) ij) :
      p.val ∉ interior (Cells ij.1 ij.2) := by
    apply MetricGluing.bankStackCells_boundary Cells Inner Coordinates Stack Base Gap
    · exact L.contourGraftCellInner_boundary S
    · intro bank side t ij p named
      apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
      intro j q equal
      exact L.roofCell_boundary_of_restore_mem S j q _ equal
        (L.contourGraftBaseMark_horizontal_mem_cut S bank side t)
    · intro bank e member side t ij p named
      apply MetricGluing.mappedNestedPoint_boundary Cells Inner Coordinates ?_ ij p named
      intro j q equal
      cases bank with
      | inl v => exact (Model[e]).planarCell_edge_boundary (!side) _ t j q equal
      | inr edge => exact (Model[e]).planarCell_tail_boundary (!side) t j q equal
    · exact seam
  apply boundary ij p
  rcases seam with ⟨q, h⟩ | ⟨q, h⟩
  · exact Or.inl ⟨q, (L.contourGraftClosedSeams_relation S _ _).mp h⟩
  · exact Or.inr ⟨q, (L.contourGraftClosedSeams_relation S _ _).mp h⟩

/-- The graft contains a genuine flat metric neighborhood around every cell interior point. -/
theorem contourGraft_cell_interior_chart (ij : Σ i, Index i) (p : Raw ij)
    (inside : p.val ∈ interior (Cells ij.1 ij.2)) :
    HasMetricBallChart Plane (L.contourGraftClosedSeamsIsometry S
      (MetricGluing.of Raw (Seams).relation ij p)) := by
  exact (MetricGluing.hasMetricBallChart_of_cell_interior
    (fun ij : Σ i, Index i => Cells ij.1 ij.2) (Seams).relation
    (L.contourGraftClosedSeams_boundary S) ij p inside).isometryEquiv
    (L.contourGraftClosedSeamsIsometry S)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
