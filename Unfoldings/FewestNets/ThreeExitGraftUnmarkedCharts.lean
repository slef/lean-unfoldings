module

public import Unfoldings.FewestNets.ThreeExitGraftAddressCoverage
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Metric.BankStackUnmarkedBall

/-! A point away from all attachment banks retains its original local metric ball. -/

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

local instance graftUnmarkedChartsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Point" => MetricGluing.point Pieces Banks

private theorem contourGraft_hasMetricBallChart_of_no_address
    {Y : Type*} [MetricSpace Y] (x : MetricGluing.Total Pieces)
    (regular : HasMetricBallChart Y x.2)
    (unmarked : ∀ (addr : Addr) (valid : Valid addr), Mark addr valid ≠ x) :
    HasMetricBallChart Y (Point x) := by
  letI (a : Attachment) : MetricSpace (Param a) := contourAttachmentMetric S a
  obtain ⟨r, rpos, cover⟩ := L.contourGraft_piece_ball_cover S x
  have no_end (side : Bool) (slot : MetricGluing.BankStackSlot Stack) (t : Param slot.1) :
      EndAt side slot t ≠ x := by
    rw [← MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot t]
    exact unmarked (Named side slot t) _
  exact MetricGluing.bankStack_hasMetricBallChart_of_unmarked Pieces Stack Base Gap x regular
    (fun slot t => ⟨no_end false slot t, no_end true slot t⟩)
    (L.isClosedEmbedding_contourBaseMark S) (isClosedEmbedding_contourGapMark S) rpos cover

/-- An interior point of a source gap has a whole planar metric ball in the
completed graft, even when the point is on a seam of the gap's polygonal cells. -/
theorem contourGraft_gap_interior_chart (e : Event) (x : Pieces (some e))
    (inside : x.val ∈ interior Model[e].region) :
    HasMetricBallChart ℂ (Point ⟨some e, x⟩) := by
  apply L.contourGraft_hasMetricBallChart_of_no_address S ⟨some e, x⟩
  · obtain ⟨r, rpos, covers⟩ := Metric.isOpen_iff.mp isOpen_interior x.val inside
    exact PolygonalPoint.hasMetricBallChart_of_ball rpos (covers.trans interior_subset)
  · rintro ⟨a, tag, side, t⟩ valid equal
    cases tag with
    | none => cases congrArg Sigma.fst equal
    | some g =>
      have same : g = e := Option.some.inj (congrArg Sigma.fst equal)
      subst g
      have mark : Gap a e valid side t = x := eq_of_heq (Sigma.mk.inj equal).2
      have address := contourGraftGapMark_eq_intrinsicAddressPoint S a e valid side t
      have boundary : x.val ∈ frontier Model[e].region := by
        rw [← mark, address]
        exact (Model[e].addressFrontier (!side)
          (PotentialCutForest.contourGapAddress Fcut S.contour a e valid t)).property
      exact boundary.2 inside

/-- A locally regular point of the whole roof off its cut keeps the original
metric ball in the completed graft. -/
theorem contourGraft_roof_off_cut_chart (x : L.whole.Cut)
    (outside : Cap.horizontal (restore x).val ∉ R.wholeCarrier)
    (regular : HasMetricBallChart Plane x) :
    HasMetricBallChart Plane (Point ⟨none, x⟩) := by
  apply L.contourGraft_hasMetricBallChart_of_no_address S ⟨none, x⟩ regular
  rintro ⟨a, tag, side, t⟩ valid equal
  cases tag with
  | some _ => cases congrArg Sigma.fst equal
  | none =>
    have same : Base a side t = x := eq_of_heq (Sigma.mk.inj equal).2
    exact outside (same ▸ L.contourGraftBaseMark_horizontal_mem_cut S a side t)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
