module

public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Geometry.OrientedBankGapTailHalfPlane
public import Unfoldings.Metric.BankStackCurveMetric
public import Unfoldings.Metric.BankStackSeamExcision

/-! Forward exit banks on both sides of each positive tail slot fill one planar ball. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

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

local instance graftTailSeamsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right

local notation "Exit" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Point" => MetricGluing.point Pieces Banks
local notation "LeftCurve" => bankStackLeftCurve Stack Pieces Base Gap
local notation "RightCurve" => bankStackRightCurve Stack Pieces Base Gap

private def tailBankChart {X : Type*} [EMetricSpace X] (bank : ℝ≥0 → X)
    (t : ℝ≥0) (occupied : Bool) : Prop :=
  ∃ speed : ℝ, 0 < speed ∧
    (∀ s u, edist (bank s) (bank u) = ENNReal.ofReal speed * edist s u) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank t occupied (fun s => (s.val - t.val) * speed) r)

private theorem tailBaseBankChart (e : Exit) (side occupied : Bool) (t : ℝ≥0) :
    tailBankChart (Base (.inr e) side) t occupied := by
  let C := L.contourTerminalContinuation S.higher S.contour S.starts e
  let bank := C.mark side
  let speed := Dilation.ratio bank
  change tailBankChart bank t occupied
  have speed_positive : 0 < speed.val := Dilation.ratio_pos bank
  refine ⟨speed.val, speed_positive, ?_, C.normalized_chart side occupied t⟩
  intro s u
  have ofReal_speed : ENNReal.ofReal speed.val = (speed : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  exact (Dilation.edist_eq bank s u).trans
    (congrArg (fun r : ℝ≥0∞ => r * edist s u) ofReal_speed.symm)

private theorem tailGapBankChart (e : Exit) (event : Event) (saved : event ∈ Stack (.inr e))
    (side occupied : Bool) (t : ℝ≥0) (positive : 0 < t) :
    tailBankChart (Gap (.inr e) event saved side) t occupied := by
  let gap := S.gaps event
  let model := gap.model
  let speed := ‖(model.bank (!side)).direction‖
  have genuine : (model.bank (!side)).direction ≠ 0 := by
    cases side
    · exact gap.second_nonzero
    · exact gap.first_nonzero
  change tailBankChart (model.tailPoint (!side)) t occupied
  refine ⟨speed, norm_pos_iff.mpr genuine, ?_, gap.exists_model_tail_normalized_chart (!side) occupied t positive⟩
  intro s u
  simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using model.edist_tailPoint (!side) s u

private theorem tailGraftSlot_charts (e : Exit) (k : Fin ((Stack (.inr e)).length + 1))
    (t : ℝ≥0) (positive : 0 < t) :
    let slot : BankStackSlot Stack := ⟨.inr e, k⟩
    tailBankChart (LeftCurve slot) t false ∧ tailBankChart (RightCurve slot) t true := by
  let slot : BankStackSlot Stack := ⟨.inr e, k⟩
  let chart (occupied : Bool) (q : Σ j, ℝ≥0 → Pieces j) := tailBankChart q.2 t occupied
  refine ⟨?_, ?_⟩
  · change chart false (bankStackLeftData Stack Pieces Base Gap slot)
    unfold bankStackLeftData
    split
    · exact L.tailBaseBankChart S e false false t
    · exact tailGapBankChart S e _ (List.getElem_mem _) true false t positive
  · change chart true (bankStackRightData Stack Pieces Base Gap slot)
    unfold bankStackRightData
    split
    · exact tailGapBankChart S e _ (List.getElem_mem _) false true t positive
    · exact L.tailBaseBankChart S e true true t

set_option maxHeartbeats 1700000 in
/-- Every positive point of an actual tail slot has a whole planar metric ball. -/
theorem contourGraft_tailSeam_chart (e : Exit) (k : Fin ((Stack (.inr e)).length + 1))
    (t : ℝ≥0) (positive : 0 < t) :
    HasMetricBallChart ℂ (Point (Left ⟨.inr e, k⟩ t)) := by
  let slot : BankStackSlot Stack := ⟨.inr e, k⟩
  let param (x : Param slot.1) : ℝ := x.val
  letI (b : Attachment) : MetricSpace (Param b) := contourAttachmentMetric S b
  obtain ⟨⟨speed, speed_pos, lm, r₁, ⟨left⟩⟩, ⟨speed₂, speed₂_pos, rm, r₂, ⟨right⟩⟩⟩ :=
    L.tailGraftSlot_charts S e k t positive
  have unit : edist (0 : ℝ≥0) 1 = 1 := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num
  have same_metric := bankStackCurves_same_metric Stack Pieces Base Gap
    (L.edist_contourBaseMark_sides S) (L.edist_contourGapMark_eq_base S) slot 0 1
  have lengths := (lm 0 1).symm.trans (same_metric.trans (rm 0 1))
  rw [unit, mul_one, mul_one] at lengths
  have same_speed : speed = speed₂ :=
    (ENNReal.ofReal_eq_ofReal_iff speed_pos.le speed₂_pos.le).mp lengths
  subst speed₂
  have distance (s : ℝ≥0) :
      ENNReal.ofReal speed * edist t s = ENNReal.ofReal (|s.val - t.val| * speed) := by
    have time : edist t s = ENNReal.ofReal (|s.val - t.val|) := by
      rw [edist_dist]
      change ENNReal.ofReal (dist t.val s.val) = _
      rw [Real.dist_eq, abs_sub_comm]
    rw [time, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have inside : param t ∈ interior (Set.range param) := by
    change t.val ∈ interior (Set.range ((↑) : ℝ≥0 → ℝ))
    have range : Set.range ((↑) : ℝ≥0 → ℝ) = Set.Ici 0 := by
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact s.property
      · intro nonnegative
        exact ⟨⟨x, nonnegative⟩, rfl⟩
    rw [range, interior_Ici]
    exact positive
  obtain ⟨radius, cover_pos, cover⟩ := L.contourGraft_piece_ball_cover S (Left slot t)
  exact bankStack_bankSlot_hasMetricBallChart Pieces Stack Base Gap slot t param
    (contourGraft_stack_nodup S) (L.contourGraft_strictMarks_unique S (.inr e) t positive)
    (L.isClosedEmbedding_contourBaseMark S) (isClosedEmbedding_contourGapMark S) cover_pos cover
    left right speed_pos inside (fun s => (lm t s).trans (distance s))
    (fun s => (rm t s).trans (distance s))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
