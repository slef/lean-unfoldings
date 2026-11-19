module

public import Unfoldings.Roof.CompatibleContourTerminalSeamClasses
public import Unfoldings.Roof.CompatibleContourBankClosedSeams
public import Unfoldings.Roof.CompatibleTerminalNormalizedChart
public import Unfoldings.Geometry.OrientedBankGapTailHalfPlane

/-! Both original banks of each terminal slot have normalized half-plane charts. -/

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

local instance contourTerminalBankChartMeshFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourOpenedBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance contourTerminalBankChartWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Models" => fun event => OrientedBankGap.model (geometry event)

local notation "Pieces" => K.compatibleContourGraftPiece compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour starts W Models
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Base" => K.compatibleContourBaseMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models
local notation "Gap" => K.compatibleContourGapMark compact nonempty R no_boundary level higher M
  positive inner_disk beta acute contour starts W Models


local notation "Edge" => TriangleComplex.ContourTerminalEdge D Selection
local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour

/-- A terminal bank chart retains its forward coordinates and whole-tail metric. -/
def TerminalBankChart {X : Type*} [EMetricSpace X]
    (bank : ℝ≥0 → X) (t : ℝ≥0) (occupied : Bool) : Prop :=
  ∃ speed : ℝ, 0 < speed ∧
    (∀ s u, edist (bank s) (bank u) = ENNReal.ofReal speed * edist s u) ∧
    ∃ r, Nonempty (BankHalfPlaneChart bank t occupied (fun s => (s.val - t.val) * speed) r)

private theorem compatibleContourTerminalBase_chart
    (edge : Edge) (side occupied : Bool) (t : ℝ≥0) :
    TerminalBankChart (Base (.inr edge) side) t occupied := by
  let root := K.compatibleMeshTerminalRoot compact nonempty R no_boundary level higher M
    positive inner_disk beta acute edge.val ((D).contourTerminalEdge_positive Selection edge)
  let τ : ℝ≥0 := ⟨R.terminalTime level root, (R.terminalTime_pos level higher root).le⟩
  let d := K.compatibleContourTerminalSpeed compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour starts W edge
  let p := forwardBankParameter τ d
  let c := ‖R.exterior.spatialDirection (R.terminalIndex root)‖
  have dpos : 0 < d.val := K.compatibleContourTerminalSpeed_positive compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W edge
  have cpos : 0 < c := norm_pos_iff.mpr (R.exterior.spatialDirection_ne_zero _)
  obtain ⟨label, same⟩ := K.compatibleContourTerminalMark_wholeBank compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W edge side
  let bank := K.wholeTerminalBank compact nonempty R no_boundary W root label
  have agrees : Base (.inr edge) side = bank ∘ p := funext same
  have ray_positive : 0 < (p t).val := (R.terminalTime_pos level higher root).trans_le
    (le_add_of_nonneg_right (mul_nonneg d.property t.property))
  obtain ⟨radius, ⟨C⟩⟩ := K.exists_wholeTerminalBank_normalized_chart compact nonempty R
    no_boundary W root label occupied (p t) ray_positive
  refine ⟨d.val * c, mul_pos dpos cpos, ?_, radius, ?_⟩
  · intro s u
    have factor : ENNReal.ofReal (d.val * c) =
        (‖R.exterior.spatialDirection (R.terminalIndex root)‖₊ : ℝ≥0∞) * d := by
      rw [ENNReal.ofReal_mul d.property,
        (show ENNReal.ofReal d.val = (d : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal), mul_comm]
      exact congrArg (fun a : ℝ≥0∞ => a * (d : ℝ≥0∞)) (by
        simp only [c, ofReal_norm, enorm_eq_nnnorm])
    exact (K.edist_compatibleContourTerminalMark compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W edge side s u).trans
      (congrArg (fun a => a * edist s u) factor.symm)
  · rw [agrees]
    refine ⟨⟨C.positive, C.chart, C.centered, ?_⟩⟩
    intro s near
    refine (C.parameter (p s) near).trans (congrArg Complex.ofReal ?_)
    change ((τ.val + d.val * s.val) - (τ.val + d.val * t.val)) * c =
      (s.val - t.val) * (d.val * c)
    ring

private theorem compatibleContourTerminalGap_chart
    (edge : Edge) (event : Event) (member : event ∈ Stack (.inr edge))
    (side occupied : Bool) (t : ℝ≥0) (positive_time : 0 < t) :
    TerminalBankChart (Gap (.inr edge) event member side) t occupied := by
  let G := geometry event
  let speed := ‖(G.model.bank side).direction‖
  have nonzero : (G.model.bank side).direction ≠ 0 := by
    cases side
    · exact G.first_nonzero
    · exact G.second_nonzero
  refine ⟨speed, norm_pos_iff.mpr nonzero, ?_, ?_⟩
  · intro s u
    change edist (G.model.tailPoint side s) (G.model.tailPoint side u) =
      ENNReal.ofReal speed * edist s u
    simpa only [speed, ofReal_norm, enorm_eq_nnnorm] using G.model.edist_tailPoint side s u
  · exact G.exists_model_tail_normalized_chart side occupied t positive_time

/-- The original two banks of any terminal stack slot have oppositely occupied charts. -/
theorem compatibleContourTerminalSlot_charts
    (edge : Edge) (i : Fin ((Stack (.inr edge)).length + 1)) (t : ℝ≥0)
    (positive_time : 0 < t) :
    let slot : BankStackSlot Stack := ⟨.inr edge, i⟩
    TerminalBankChart (bankStackLeftCurve Stack Pieces Base Gap slot) t false ∧
      TerminalBankChart (bankStackRightCurve Stack Pieces Base Gap slot) t true := by
  let slot : BankStackSlot Stack := ⟨.inr edge, i⟩
  have base (side occupied : Bool) := K.compatibleContourTerminalBase_chart compact nonempty R
    no_boundary level higher M positive inner_disk beta acute contour starts W geometry edge
      side occupied t
  have gap (event : Event) (member : event ∈ Stack (.inr edge)) (side occupied : Bool) :=
    K.compatibleContourTerminalGap_chart compact nonempty R no_boundary level higher M positive
      inner_disk beta acute contour starts W geometry edge event member side occupied t
        positive_time
  let P (occupied : Bool) (q : Σ j, ℝ≥0 → Pieces j) := TerminalBankChart q.2 t occupied
  refine ⟨?_, ?_⟩
  · change P false (bankStackLeftData Stack Pieces Base Gap slot)
    unfold bankStackLeftData
    split
    · exact base false false
    · exact gap _ (List.getElem_mem _) true false
  · change P true (bankStackRightData Stack Pieces Base Gap slot)
    unfold bankStackRightData
    split
    · exact gap _ (List.getElem_mem _) false true
    · exact base true true

end Unfoldings.ConvexRoof
