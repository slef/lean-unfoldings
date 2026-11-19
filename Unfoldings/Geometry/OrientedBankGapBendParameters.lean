module

public import Unfoldings.Cone.DirectedIntervalChart
public import Unfoldings.Geometry.OrientedBankGapBendChart
public import Unfoldings.Geometry.RadialCornerFrameParameters

/-! The genuine adjacent closed edges use exact arclength rays in the bend chart. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : OrientedBankGap first second)
  (side : Bool) (k : Fin n)

local notation "B" => BankGapModel.bank G.model side
local notation "p" => PolygonalChain.vertex (PolygonalRay.chain B) k.succ.castSucc
local notation "d" => (p - PolygonalRay.start B)
local notation "inEdge" => PolygonalChain.edge (PolygonalRay.chain B) k.castSucc
local notation "outEdge" => PolygonalChain.edge (PolygonalRay.chain B) k.succ
local notation "width" => cond side
  (radialRightCornerWidth d inEdge outEdge) (radialLeftCornerWidth d inEdge outEdge)
local notation "frame" => cond side
  (radialRightCornerFrame d inEdge) (radialLeftCornerFrame d outEdge)
local notation "tip" => BankGapModel.edgePoint G.model side k.succ 0

/-- The actual incoming edge has reversed time from the bend. The outgoing edge
has forward time from it. Both agree with the same physical centered sector chart. -/
theorem bend_chart_bank_coordinates (radial_ne : d ≠ 0) (in_ne : inEdge ≠ 0)
    (out_ne : outEdge ≠ 0) {r : ℝ} (pos : 0 ≤ width)
    (A : Metric.eball tip (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (closedAngularSectorOrigin pos) (ENNReal.ofReal r))
    (physical : ∀ y, p + frame (A y).val.val = y.val.val) :
    (∀ (t : unitInterval)
        (near : edist (G.model.edgePoint side k.castSucc t) tip < ENNReal.ofReal r),
      (A ⟨G.model.edgePoint side k.castSucc t, near⟩).val.val =
        if side then (((1 - t.val) * ‖inEdge‖ : ℝ) : ℂ)
        else ((1 - t.val) * ‖inEdge‖) • polarRay width) ∧
    (∀ (t : unitInterval) (near : edist (G.model.edgePoint side k.succ t) tip < ENNReal.ofReal r),
      (A ⟨G.model.edgePoint side k.succ t, near⟩).val.val =
        if side then (t.val * ‖outEdge‖) • polarRay width
        else (((t.val * ‖outEdge‖ : ℝ) : ℂ))) := by
  constructor
  · intro t near
    apply (frame).injective
    apply add_left_cancel (a := p)
    refine (physical ⟨G.model.edgePoint side k.castSucc t, near⟩).trans ?_
    have along : (B).chain.point k.castSucc t = p + (1 - t.val) • (-inEdge) := by
      have finish : (B).chain.vertex k.castSucc.succ = p :=
        congrArg (B).chain.vertex (Fin.succ_castSucc k)
      change AffineMap.lineMap ((B).chain.vertex k.castSucc.castSucc)
        ((B).chain.vertex k.castSucc.succ) t.val = _
      rw [PolygonalChain.edge, AffineMap.lineMap_apply_module', finish]
      module
    have calibrated : frame (if side then (((1 - t.val) * ‖inEdge‖ : ℝ) : ℂ)
        else ((1 - t.val) * ‖inEdge‖) • polarRay width) =
        (1 - t.val) • (-inEdge) := by
      have left := radialLeftCornerFrame_terminal_length d inEdge outEdge radial_ne in_ne
        (1 - t.val)
      have right := radialRightCornerFrame_real_length d inEdge radial_ne in_ne (1 - t.val)
      cases side
      · exact left
      · exact right
    exact along.trans (congrArg (p + ·) calibrated.symm)
  · intro t near
    apply (frame).injective
    apply add_left_cancel (a := p)
    refine (physical ⟨G.model.edgePoint side k.succ t, near⟩).trans ?_
    have along : (B).chain.point k.succ t = p + t.val • outEdge := by
      change AffineMap.lineMap p ((B).chain.vertex k.succ.succ) t.val = _
      rw [AffineMap.lineMap_apply_module', add_comm]
      rfl
    have calibrated : frame (if side then (t.val * ‖outEdge‖) • polarRay width
        else (((t.val * ‖outEdge‖ : ℝ) : ℂ))) = t.val • outEdge := by
      have left := radialLeftCornerFrame_real_length d outEdge radial_ne out_ne t.val
      have right := radialRightCornerFrame_terminal_length d inEdge outEdge radial_ne out_ne t.val
      cases side
      · exact left
      · exact right
    exact along.trans (congrArg (p + ·) calibrated.symm)

/-- A genuine bend has a whole marked angular chart with its original arclength
parameters along both incident finite edges. -/
theorem exists_model_bend_marked_chart (genuine : ∀ i, (B).chain.edge i ≠ 0)
    (radial : 0 < inner ℝ d outEdge) :
    ∃ (pos : 0 < width) (r : ℝ) (rpos : 0 < r)
      (A : Metric.eball tip (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (closedAngularSectorOrigin pos.le) (ENNReal.ofReal r)),
      (A ⟨tip, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩).val =
        closedAngularSectorOrigin pos.le ∧
      (∀ (t : unitInterval)
        (near : edist (G.model.edgePoint side k.castSucc t) tip < ENNReal.ofReal r),
        (A ⟨G.model.edgePoint side k.castSucc t, near⟩).val.val =
          if side then (((1 - t.val) * ‖inEdge‖ : ℝ) : ℂ)
          else ((1 - t.val) * ‖inEdge‖) • polarRay width) ∧
      ∀ (t : unitInterval)
        (near : edist (G.model.edgePoint side k.succ t) tip < ENNReal.ofReal r),
        (A ⟨G.model.edgePoint side k.succ t, near⟩).val.val =
          if side then (t.val * ‖outEdge‖) • polarRay width
          else (((t.val * ‖outEdge‖ : ℝ) : ℂ)) := by
  obtain ⟨pos, small, r, rpos, geometric, centered, physical⟩ :=
    G.exists_model_bend_chart side k genuine radial
  let oldWidth := if side then radialRightCornerWidth d inEdge outEdge
    else radialLeftCornerWidth d inEdge outEdge
  have same : oldWidth = width := (Bool.cond_eq_ite _ _ _).symm
  let F := bisectedSectorFan oldWidth pos small
  have angle : F.totalAngle = width := (bisectedSectorFan_totalAngle _ _ _).trans same
  have positive : 0 < width := same ▸ pos
  let E := (F.intrinsicAngularSectorIsometryEquiv
      ((bisectedSectorFan_totalAngle _ _ _).trans_lt small)).trans
    (PolygonalPoint.congrIsometryEquiv (congrArg closedAngularSector angle))
  have E_center : E F.origin = closedAngularSectorOrigin positive.le := by
    apply PolygonalPoint.ext
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
      AngularFan.intrinsicAngularSectorIsometryEquiv_val, AngularFan.develop_origin]
    rfl
  let A := geometric.trans (basedEBallIsometry E F.origin _ E_center (ENNReal.ofReal r))
  have trace (y : Metric.eball tip (ENNReal.ofReal r)) :
      p + frame (A y).val.val = y.val.val := by
    change p + frame (E (geometric y).val).val = _
    rw [IsometryEquiv.trans_apply, PolygonalPoint.congrIsometryEquiv_val,
      AngularFan.intrinsicAngularSectorIsometryEquiv_val]
    simpa only [Bool.cond_eq_ite] using physical y
  have radial_ne : d ≠ 0 := by
    intro zero
    rw [zero, inner_zero_left] at radial
    exact (lt_irrefl 0 radial)
  refine ⟨positive, r, rpos, A, ?_, G.bend_chart_bank_coordinates side k radial_ne
    (genuine k.castSucc) (genuine k.succ) positive.le A trace⟩
  exact (congrArg E centered).trans E_center

end Unfoldings.OrientedBankGap
