module

public import Unfoldings.FewestNets.ThreeExitGraftClosedSeams
public import Unfoldings.Metric.FinitePartialLabels
public import Unfoldings.Metric.BankStackLabels
public import Unfoldings.Metric.FiniteLabelClasses
public import Unfoldings.Metric.MappedBankGraftExactness
public import Unfoldings.Metric.MappedBankGraftBallCover

/-! Spatial boundary labels give finite exact seam classes in the complete source graft. -/

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

local instance graftLabelsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Path[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "Fold" => contourGraftPieceCollapse L S
local notation "Seams" => contourGraftClosedSeams L S
local notation "original" => MetricGluing.mappedNestedPoint Cells Inner Coordinates
local notation "Label" => Space ⊕ (Event × ℂ)

/-- A source gap's frontier point carries its exact original spatial address. -/
def contourGraftFrontierLabel (e : Event) (x : frontier Model[e].region) : Space :=
  Fold (some e) ⟨x.val, Model[e].closed.frontier_subset x.property⟩

local notation "FrontierAt" => contourGraftFrontierLabel L S

/-- Over one physical address, a gap has at most its two original boundary points. -/
theorem finite_contourGraftFrontierLabel (e : Event) (p : Space) :
    {x : frontier Model[e].region | FrontierAt e x = p}.Finite := by
  classical
  let fiber := {x : frontier Model[e].region | FrontierAt e x = p}
  by_cases exists_point : fiber.Nonempty
  · obtain ⟨x, equal⟩ := exists_point
    let y : PolygonalPoint Model[e].region := ⟨x.val, Model[e].closed.frontier_subset x.property⟩
    have physical : p ∈ (Path[e]).carrier := by
      change (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e) y).val = p
        at equal
      rw [← equal]
      exact (R.contourSourceGapCollapse level M S.higher S.contour S.starts e (S.gaps e) y).property
    obtain ⟨a, address⟩ := (Path[e]).exists_address physical
    apply (Set.finite_range (fun side => Model[e].addressFrontier side a)).subset
    intro z point
    let q : PolygonalPoint Model[e].region := ⟨z.val, Model[e].closed.frontier_subset z.property⟩
    have match_address : Fold (some e) q = (Path[e]).addressPoint a := point.trans address.symm
    obtain ⟨side, same⟩ :=
      ((R.hasMarkedCollapseFibers_contourSourceGapCollapse level M S.higher S.contour
        S.starts e (S.gaps e)).2 a).2 q z.property match_address
    exact ⟨side, Subtype.ext (congrArg PolygonalPoint.val same).symm⟩
  · change fiber.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp exists_point]
    exact Set.finite_empty

/-- Interior gap points retain their gap and local coordinate labels. -/
def contourGraftPieceLabel : (i : Option Event) → Pieces i → Label
  | none, x => .inl (restore x).val
  | some e, x => MetricGluing.partialLabel (frontier Model[e].region) (FrontierAt e) e x.val

local notation "LabelAt" => contourGraftPieceLabel L S

private theorem contourGapMark_frontier (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (t : Param a) :
    (Gap a e member side t).val ∈ frontier Model[e].region := by
  cases a with
  | inl v =>
    let i := (D).contourGapBankIndex Selection S.contour v.val v.property e
      (((D).mem_contourEdgeGapStack Selection S.contour v.val e).mpr
        (((D).mem_contourSavedGapStack Selection S.contour v.val e).mp member))
    exact (Model[e].addressFrontier (!side) (.inl (i, t))).property
  | inr edge =>
    exact (Model[e].addressFrontier (!side) (.inr t)).property

/-- Every attachment keeps the physical address of the original bank. -/
def contourGraftBankLabel (a : Attachment) (t : Param a) : Label :=
  .inl (restore (Base a false t)).val

local notation "BankLabel" => contourGraftBankLabel L S

private theorem contourBaseMark_label (a : Attachment) (side : Bool) (t : Param a) :
    LabelAt none (Base a side t) = (BankLabel) a t := by
  cases side
  · rfl
  · exact congrArg Sum.inl (L.restore_contourBaseMark_sides S a t).symm

private theorem contourGapMark_label (a : Attachment) (e : Event)
    (member : e ∈ Stack a) (side : Bool) (t : Param a) :
    LabelAt (some e) (Gap a e member side t) = (BankLabel) a t := by
  have h := contourGapMark_frontier S a e member side t
  change MetricGluing.partialLabel (frontier Model[e].region) (FrontierAt e) e
    (Gap a e member side t).val = _
  rw [MetricGluing.partialLabel_of_mem _ _ _ _ h]
  exact (congrArg Sum.inl (L.contourGraftPieceCollapse_gap_eq S a e member side t)).trans
    (L.contourBaseMark_label S a side t)

def contourGraftCellLabel (x : MetricGluing.Total Raw) : Label :=
  let named := original x
  LabelAt named.1 named.2

local notation "CellLabel" => contourGraftCellLabel L S

/-- Internal seams preserve the piece point and outer seams preserve its original bank label. -/
theorem contourGraftCellLabel_seam (x y : MetricGluing.Total Raw)
    (seam : (Seams).relation x y) : CellLabel x = CellLabel y := by
  have joined := (L.contourGraftClosedSeams_relation S x y).mp seam
  cases joined with
  | «inside» i p q glued =>
    exact congrArg (fun z => LabelAt i (Coordinates i z))
      (MetricGluing.point_eq_of_glue _ glued)
  | between p q glued =>
    exact MetricGluing.bankStackSeams_label Pieces Stack Base Gap (fun z => LabelAt z.1 z.2)
      (BankLabel) (L.contourBaseMark_label S) (L.contourGapMark_label S) _ _ glued

/-- The finite planar cells have finite label fibers even when the actual
spatial collapse contracts an entire gap interior. -/
theorem finite_contourGraftCellLabel_fiber (ij : Σ i, Index i) (label : Label) :
    {p : Raw ij | CellLabel ⟨ij, p⟩ = label}.Finite := by
  obtain ⟨i, j⟩ := ij
  cases i with
  | none =>
    have injective : Function.Injective (fun p : Cells none j => CellLabel ⟨⟨none, j⟩, p⟩) := by
      intro p q same
      have equal : (L.whole.partition.cellIsometryEquiv j p).val =
          (L.whole.partition.cellIsometryEquiv j q).val := Sum.inl.inj same
      exact (L.whole.partition.cellIsometryEquiv j).injective (Subtype.ext equal)
    exact (show {p : Cells none j | CellLabel ⟨⟨none, j⟩, p⟩ = label}.Subsingleton from
      fun _ first _ last => injective (first.trans last.symm)).finite
  | some e =>
    have finite := MetricGluing.finite_partialLabel_fiber (frontier Model[e].region)
      (FrontierAt e) e (L.finite_contourGraftFrontierLabel S e) label
    have injective : Function.Injective (fun p : Model[e].planarCells j =>
        Complex.orthonormalBasisOneI.repr.symm p.val) := by
      intro p q same
      exact Subtype.ext (Complex.orthonormalBasisOneI.repr.symm.injective same)
    exact finite.preimage injective.injOn

/-- Each original route-equivalence class has finitely many points per cell. -/
theorem finite_contourGraftClosedSeams_class (x : MetricGluing.Total Raw) (ij : Σ i, Index i) :
    (MetricGluing.classIn Raw (Seams).relation x ij).Finite :=
  MetricGluing.finite_classIn_of_finite_label_fibers (Seams).relation CellLabel
    (L.contourGraftCellLabel_seam S) (L.finite_contourGraftCellLabel_fiber S) x ij

/-- The route quotient has exactly the declared seam identifications. -/
theorem contourGraftClosedSeams_exact : MetricGluing.Exact Raw (Seams).relation :=
  (Seams).exact_of_finite_classes (L.finite_contourGraftClosedSeams_class S)

local notation "Banks" => MetricGluing.bankSeams Left Right

/-- The complete graft has exactly its declared intrinsic piece identifications. -/
theorem contourGraft_exact : MetricGluing.Exact Pieces Banks := by
  apply MetricGluing.exact_of_presentation Raw Pieces (Seams).relation Banks original
    (MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates)
    (L.contourGraftClosedSeamsIsometry S) (fun _ => rfl)
    (L.contourGraftClosedSeams_exact S)
  intro x y joined
  exact MetricGluing.mappedBankGraftCells_eqvGen_image Cells Inner Coordinates Left Right x y
    ((L.contourGraftClosedSeams_relation S x y).mp joined)

/-- Near a graft point, every piece point is close to a literal representative
of the center in its own piece. -/
theorem contourGraft_piece_ball_cover (x : MetricGluing.Total Pieces) :
    ∃ ε > 0, ∀ r, 0 < r → r ≤ ε → ∀ b : MetricGluing.Total Pieces,
      edist (MetricGluing.point Pieces Banks x) (MetricGluing.point Pieces Banks b) <
        ENNReal.ofReal r →
      ∃ c : Pieces b.1, Relation.EqvGen Banks x ⟨b.1, c⟩ ∧ edist c b.2 < ENNReal.ofReal r := by
  obtain ⟨a, rfl⟩ := MetricGluing.mappedNestedPoint_surjective Cells Inner Coordinates x
  exact MetricGluing.exists_mappedBankGraft_piece_cover Cells Inner Coordinates Left Right Seams
    (L.contourGraftClosedSeams_relation S) a (L.finite_contourGraftClosedSeams_class S a)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
