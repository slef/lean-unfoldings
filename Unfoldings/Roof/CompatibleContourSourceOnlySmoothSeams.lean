module

public import Unfoldings.Roof.CompatibleContourSourceOnlySmoothMarks
public import Unfoldings.Roof.CompatibleContourSourceOnlyLabels
public import Unfoldings.Roof.CompatibleContourFiniteBankCharts
public import Unfoldings.Roof.CompatibleContourTerminalBankCharts
public import Unfoldings.Metric.BankStackSeamExcision

/-! Whole planar balls at ordinary finite and true-tail source-only seams. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open MetricGluing

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

local instance sourceOnlySmoothSeamIndexFintype : Fintype (T).Index :=
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

local instance sourceOnlySmoothSeamWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
variable (geometry : ∀ event :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour, OrientedBankGap
  (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts event)
  (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
    inner_disk beta acute contour starts event))

local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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
local notation "Regular" => K.compatibleContourBankParameterInterior compact nonempty R
  no_boundary level higher M positive inner_disk beta acute
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "LC" => MetricGluing.bankStackLeftCurve Stack Pieces Base Gap
local notation "RC" => MetricGluing.bankStackRightCurve Stack Pieces Base Gap

private def bankTime (bank : Attachment) : ParamAt bank → ℝ :=
  match bank with
  | .inl _ => Subtype.val
  | .inr _ => Subtype.val

local notation "Time" => bankTime K compact nonempty R no_boundary level higher M positive
  inner_disk beta acute

omit beta acute in
private def calibratedBank {P X : Type*} [EMetricSpace P] [EMetricSpace X]
    (bank : P → X) (param : P → ℝ) (t : P) (occupied : Bool) : Prop :=
  ∃ speed : ℝ, 0 < speed ∧
    (∀ s u, edist (bank s) (bank u) = ENNReal.ofReal speed * edist s u) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank t occupied (fun s => (param s - param t) * speed) r)

private theorem roof_bank_chart (bank : Attachment) (t : ParamAt bank) (regular : Regular bank t)
    (side occupied : Bool) : calibratedBank (Base bank side) (Time bank) t occupied := by
  cases bank with
  | inl v =>
    exact K.compatibleContourParentMark_finiteBankChart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W v side occupied t regular
  | inr e =>
    exact K.compatibleContourTerminalMark_terminalBankChart compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W e side occupied t

private theorem gap_bank_chart (bank : Attachment) (t : ParamAt bank) (regular : Regular bank t)
    (e : Event) (member : e ∈ Stack bank) (side occupied : Bool) :
    calibratedBank (Gap bank e member side) (Time bank) t occupied := by
  let g := geometry e
  have entire := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts models e
  cases bank with
  | inl v =>
    let i := (D).contourGapBankIndex Selection contour v.val v.property e
      (((D).mem_contourEdgeGapStack Selection contour v.val e).mpr
        (((D).mem_contourSavedGapStack Selection contour v.val e).mp member))
    let speed := ‖(g.model.bank (!side)).chain.edge i‖
    refine ⟨speed, norm_pos_iff.mpr (entire (!side) i), ?_, ?_⟩
    · intro s u
      change edist (g.model.edgePoint (!side) i s) (g.model.edgePoint (!side) i u) =
        ENNReal.ofReal speed * edist s u
      simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using g.model.edist_edgePoint (!side) i s u
    · exact g.exists_model_edge_normalized_chart entire (!side) occupied i t regular
  | inr edge =>
    let speed := ‖(g.model.bank (!side)).direction‖
    have nonzero : (g.model.bank (!side)).direction ≠ 0 :=
      (K.compatibleContourSourceOnlyBank_direction_eq_last compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models e (!side)).trans_ne
          (entire (!side) _)
    refine ⟨speed, norm_pos_iff.mpr nonzero, ?_, ?_⟩
    · intro s u
      change edist (g.model.tailPoint (!side) s) (g.model.tailPoint (!side) u) =
        ENNReal.ofReal speed * edist s u
      simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using g.model.edist_tailPoint (!side) s u
    · exact g.exists_model_tail_normalized_chart (!side) occupied t regular

private theorem slot_charts (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1)
    (regular : Regular slot.1 t) :
    calibratedBank (LC slot) (Time slot.1) t false ∧
      calibratedBank (RC slot) (Time slot.1) t true := by
  let P (occupied : Bool) (q : Σ j, ParamAt slot.1 → Pieces j) :=
    calibratedBank q.2 (Time slot.1) t occupied
  refine ⟨?_, ?_⟩
  · change P false (MetricGluing.bankStackLeftData Stack Pieces Base Gap slot)
    unfold MetricGluing.bankStackLeftData
    split
    · exact roof_bank_chart K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W slot.1 t regular false false
    · exact gap_bank_chart K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts geometry slot.1 t regular _ (List.getElem_mem _) true false
  · change P true (MetricGluing.bankStackRightData Stack Pieces Base Gap slot)
    unfold MetricGluing.bankStackRightData
    split
    · exact gap_bank_chart K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts geometry slot.1 t regular _ (List.getElem_mem _) false true
    · exact roof_bank_chart K compact nonempty R no_boundary level higher M positive inner_disk
        beta acute contour starts W slot.1 t regular true true

private theorem edist_bankTime (bank : Attachment) (s t : ParamAt bank) :
    edist s t = ENNReal.ofReal (|Time bank t - Time bank s|) := by
  cases bank <;> rw [edist_dist]
  · change ENNReal.ofReal (dist s.val t.val) = ENNReal.ofReal |t.val - s.val|
    rw [Real.dist_eq, abs_sub_comm]
  · change ENNReal.ofReal (|s.val - t.val|) = ENNReal.ofReal |t.val - s.val|
    rw [abs_sub_comm]

private theorem bankTime_inside (bank : Attachment) (t : ParamAt bank) (regular : Regular bank t) :
    Time bank t ∈ interior (Set.range (Time bank)) := by
  cases bank with
  | inl v =>
    change t.val ∈ interior (Set.range (Subtype.val : unitInterval → ℝ))
    rwa [Subtype.range_coe, interior_Icc]
  | inr e =>
    change t.val ∈ interior (Set.range (Subtype.val : ℝ≥0 → ℝ))
    have range_eq : Set.range (Subtype.val : ℝ≥0 → ℝ) = Set.Ici 0 := by
      ext x
      exact ⟨fun ⟨s, eq⟩ => eq ▸ s.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rwa [range_eq, interior_Ici]

private theorem exists_unit_bank_spacing (bank : Attachment) :
    ∃ s u : ParamAt bank, edist s u = 1 := by
  cases bank
  · refine ⟨0, 1, ?_⟩
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num
  · refine ⟨0, 1, ?_⟩
    rw [edist_dist]
    change ENNReal.ofReal (dist (0 : ℝ) 1) = 1
    norm_num

set_option maxHeartbeats 150000 in
-- Covers refer to the original cut metric and each finite gap cell.
/-- Every strict finite or positive tail attachment point of the actual source-only
graft has a whole planar ball, including seam slots without attached gaps. -/
theorem compatibleContourSourceOnlySmoothSeam_planarBall
    (slot : MetricGluing.BankStackSlot Stack) (t : ParamAt slot.1) (regular : Regular slot.1 t) :
    HasMetricBallChart ℂ (MetricGluing.point Pieces Banks (Left slot t)) := by
  obtain ⟨⟨speed, speed_pos, lm, r₁, ⟨L⟩⟩, ⟨b, bpos, rm, r₂, ⟨B⟩⟩⟩ :=
    slot_charts K compact nonempty R no_boundary level higher M positive inner_disk beta acute
      contour starts W geometry slot t regular
  obtain ⟨s, u, distance⟩ := exists_unit_bank_spacing K compact nonempty R no_boundary level
    higher M positive inner_disk beta acute slot.1
  have same := MetricGluing.bankStackCurves_same_metric Stack Pieces Base Gap
    (K.compatibleContourSourceOnlyBaseMark_metric compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_metric compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models) slot s u
  have equal_speed : speed = b := by
    have lengths := (lm s u).symm.trans (same.trans (rm s u))
    rw [distance, mul_one, mul_one] at lengths
    exact (ENNReal.ofReal_eq_ofReal_iff speed_pos.le bpos.le).mp lengths
  subst b
  have arc (s : ParamAt slot.1) : ENNReal.ofReal speed * edist t s =
      ENNReal.ofReal (|Time slot.1 s - Time slot.1 t| * speed) := by
    rw [edist_bankTime, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  obtain ⟨ε, εpos, cover⟩ := K.compatibleContourSourceOnlyGraft_piece_ball_cover compact
    nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W models
    geometry (Left slot t)
  exact MetricGluing.bankStack_bankSlot_hasMetricBallChart Pieces Stack Base Gap slot t (Time slot.1)
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour)
    (K.compatibleContourSourceOnlyMarks_unique compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W models geometry slot.1 t regular)
    (K.compatibleContourSourceOnlyBaseMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts W)
    (K.compatibleContourSourceOnlyGapMark_isClosedEmbedding compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models)
    εpos cover L B speed_pos
    (bankTime_inside K compact nonempty R no_boundary level higher M positive inner_disk beta acute
      slot.1 t regular)
    (fun s => (lm t s).trans (arc s)) (fun s => (rm t s).trans (arc s))

end Unfoldings.ConvexRoof
