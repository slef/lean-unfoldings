module

public import Unfoldings.FewestNets.ThreeExitGraftFiniteBankCharts
public import Unfoldings.FewestNets.ThreeExitGraftStrictFiber
public import Unfoldings.FewestNets.ThreeExitGraftMarkMetrics
public import Unfoldings.Geometry.OrientedBankGapHalfPlane
public import Unfoldings.Metric.BankStackCurveMetric
public import Unfoldings.Metric.BankStackSeamExcision

/-! Both sides of each strict finite attachment slot fill one planar ball. -/

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

local instance graftFiniteSeamsIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
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

local notation "Child" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "Point" => MetricGluing.point Pieces Banks
local notation "LeftCurve" => bankStackLeftCurve Stack Pieces Base Gap
local notation "RightCurve" => bankStackRightCurve Stack Pieces Base Gap

private def finiteBankChart {X : Type*} [EMetricSpace X] (bank : unitInterval → X)
    (t : unitInterval) (occupied : Bool) : Prop :=
  ∃ speed : ℝ, 0 < speed ∧
    (∀ s u, edist (bank s) (bank u) = ENNReal.ofReal speed * edist s u) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank t occupied (fun s => (s.val - t.val) * speed) r)

private theorem finiteGapBankChart (e : Child) (event : Event)
    (saved : event ∈ Stack (.inl e)) (side occupied : Bool)
    (t : unitInterval) (strict : 0 < t ∧ t < 1) :
    finiteBankChart (Gap (.inl e) event saved side) t occupied := by
  let model := Model[event]
  have edge_member := ((D).mem_contourEdgeGapStack Selection S.contour e.val event).mpr
    (((D).mem_contourSavedGapStack Selection S.contour e.val event).mp saved)
  let i := (D).contourGapBankIndex Selection S.contour e.val e.property event edge_member
  let speed := ‖(model.bank (!side)).chain.edge i‖
  refine ⟨speed, norm_pos_iff.mpr (contourGap_edge_ne_zero S event (!side) i), ?_, ?_⟩
  · intro s u
    change edist (model.edgePoint (!side) i s) (model.edgePoint (!side) i u) =
      ENNReal.ofReal speed * edist s u
    simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using model.edist_edgePoint (!side) i s u
  · exact (S.gaps event).exists_model_edge_normalized_chart
      (contourGap_edge_ne_zero S event) (!side) occupied i t strict

private theorem finiteGraftSlot_charts (e : Child) (k : Fin ((Stack (.inl e)).length + 1))
    (t : unitInterval) (strict : 0 < t ∧ t < 1) :
    let slot : BankStackSlot Stack := ⟨.inl e, k⟩
    finiteBankChart (LeftCurve slot) t false ∧ finiteBankChart (RightCurve slot) t true := by
  let slot : BankStackSlot Stack := ⟨.inl e, k⟩
  let chart (occupied : Bool) (q : Σ j, unitInterval → Pieces j) := finiteBankChart q.2 t occupied
  refine ⟨?_, ?_⟩
  · change chart false (bankStackLeftData Stack Pieces Base Gap slot)
    unfold bankStackLeftData
    split
    · exact L.contourBaseMark_finite_halfPlaneChart S e false false t strict
    · exact finiteGapBankChart S e _ (List.getElem_mem _) true false t strict
  · change chart true (bankStackRightData Stack Pieces Base Gap slot)
    unfold bankStackRightData
    split
    · exact finiteGapBankChart S e _ (List.getElem_mem _) false true t strict
    · exact L.contourBaseMark_finite_halfPlaneChart S e true true t strict

set_option maxHeartbeats 1700000 in
/-- Every interior point of a finite attachment seam has a whole planar
metric ball in the actual graft, including slots between two source gaps. -/
theorem contourGraft_finiteSeam_chart (e : Child) (k : Fin ((Stack (.inl e)).length + 1))
    (t : unitInterval) (strict : 0 < t ∧ t < 1) :
    HasMetricBallChart ℂ (Point (Left ⟨.inl e, k⟩ t)) := by
  let slot : BankStackSlot Stack := ⟨.inl e, k⟩
  let param (x : Param slot.1) : ℝ := x.val
  letI (b : Attachment) : MetricSpace (Param b) := contourAttachmentMetric S b
  obtain ⟨⟨speed, speed_pos, lm, r₁, ⟨left⟩⟩, ⟨speed₂, speed₂_pos, rm, r₂, ⟨right⟩⟩⟩ :=
    L.finiteGraftSlot_charts S e k t strict
  have unit : edist (0 : unitInterval) 1 = 1 := by
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
  have distance (s : unitInterval) :
      ENNReal.ofReal speed * edist t s = ENNReal.ofReal (|s.val - t.val| * speed) := by
    have time : edist t s = ENNReal.ofReal (|s.val - t.val|) := by
      rw [edist_dist]
      change ENNReal.ofReal (dist t.val s.val) = _
      rw [Real.dist_eq, abs_sub_comm]
    rw [time, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  have inside : param t ∈ interior (Set.range param) := by
    change t.val ∈ interior (Set.range (Subtype.val : unitInterval → ℝ))
    rwa [Subtype.range_coe, interior_Icc]
  obtain ⟨radius, positive, cover⟩ := L.contourGraft_piece_ball_cover S (Left slot t)
  exact bankStack_bankSlot_hasMetricBallChart Pieces Stack Base Gap slot t param
    (contourGraft_stack_nodup S) (L.contourGraft_strictMarks_unique S (.inl e) t strict)
    (L.isClosedEmbedding_contourBaseMark S) (isClosedEmbedding_contourGapMark S) positive cover
    left right speed_pos inside (fun s => (lm t s).trans (distance s))
    (fun s => (rm t s).trans (distance s))

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
