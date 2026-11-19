module

public import Unfoldings.Geometry.OrientedBankGapJoinChart

/-! A single signed parameter through the named finite-to-infinite gap bank join. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

/-- Signed displacement from the join, with the final finite edge running from `-1` to `0`. -/
abbrev BankJoinTime := Set.Ici (-1 : ℝ)

/-- The last finite edge followed by the actual unbounded tail. -/
def joinedBank {X : Type*} (finite : unitInterval → X) (tail : ℝ≥0 → X)
    (t : BankJoinTime) : X :=
  if h : t.val < 0 then
    finite ⟨1 + t.val, by have := t.property; change -1 ≤ t.val at this; linarith, by linarith⟩
  else tail ⟨t.val, le_of_not_gt h⟩

@[simp] theorem joinedBank_zero {X : Type*} (finite : unitInterval → X) (tail : ℝ≥0 → X) :
    joinedBank finite tail ⟨0, by norm_num⟩ = tail 0 := by
  rw [joinedBank, dite_eq_right (lt_irrefl (0 : ℝ))]
  rfl

namespace BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : BankGapModel first second)

local notation "Bank[" side "," t "]" =>
  joinedBank (G.edgePoint side (Fin.last n)) (G.tailPoint side) t

/-- Along a straight join, the entire last finite edge and the tail share an affine trace. -/
theorem joinedBank_val (side : Bool)
    (straight : (G.bank side).direction = (G.bank side).chain.edge (Fin.last n))
    (t : BankJoinTime) :
    Bank[side,t].val = (G.bank side).chain.vertex (Fin.last (n + 1)) +
      t.val • (G.bank side).direction := by
  unfold joinedBank
  split
  · change (G.bank side).chain.point (Fin.last n) _ = _
    rw [PolygonalChain.point, AffineMap.lineMap_apply_module', add_smul, one_smul]
    let R := G.bank side
    let edge := R.chain.edge (Fin.last n)
    let start := R.chain.vertex (Fin.last n).castSucc
    let finish := R.chain.vertex (Fin.last (n + 1))
    change edge + t.val • edge + start = finish + t.val • R.direction
    have advance : edge + start = finish := sub_add_cancel _ _
    rw [straight, ← advance]
    abel
  · rfl

/-- The signed parameter through a straight gap join has the actual Euclidean speed. -/
theorem edist_joinedBank (side : Bool)
    (straight : (G.bank side).direction = (G.bank side).chain.edge (Fin.last n))
    (s t : BankJoinTime) :
    edist Bank[side,s] Bank[side,t] =
      ENNReal.ofReal (|s.val - t.val| * ‖(G.bank side).direction‖) := by
  let p := (G.bank side).chain.vertex (Fin.last (n + 1))
  let d := (G.bank side).direction
  have segment : segment ℝ Bank[side,s].val Bank[side,t].val ⊆ G.region := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨u, hu, rfl⟩
    rw [G.joinedBank_val side straight, G.joinedBank_val side straight]
    have point : AffineMap.lineMap s.val t.val u ∈ segment ℝ s.val t.val := by
      rw [segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
    let v : BankJoinTime := ⟨AffineMap.lineMap s.val t.val u,
      (convex_Ici (-1 : ℝ)).segment_subset s.property t.property point⟩
    have same : AffineMap.lineMap (p + s.val • d) (p + t.val • d) u = p + v.val • d := by
      change _ = p + AffineMap.lineMap s.val t.val u • d
      simp only [AffineMap.lineMap_apply_module', add_sub_add_left_eq_sub, ← sub_smul,
        smul_eq_mul, add_smul, smul_smul]
      abel
    have member := Bank[side,v].property
    rw [G.joinedBank_val side straight] at member
    exact same.symm ▸ member
  rw [PolygonalPoint.edist_eq_of_segment segment, G.joinedBank_val side straight,
    G.joinedBank_val side straight, edist_dist, dist_eq_norm, add_sub_add_left_eq_sub,
    ← sub_smul, norm_smul, Real.norm_eq_abs]

end BankGapModel

namespace OrientedBankGap

open MetricGluing

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : OrientedBankGap first second)

/-- The actual gap rim join has a centered half-plane chart preserving arclength on both
its last finite edge and the unbounded tail. -/
theorem exists_model_straightJoin_normalized_chart
    (side occupied : Bool) (straight : (G.model.bank side).direction =
      (G.model.bank side).chain.edge (Fin.last n))
    (genuine : ∀ i, (G.model.bank side).chain.edge i ≠ 0) :
    ∃ r, Nonempty (BankHalfPlaneChart
      (joinedBank (G.model.edgePoint side (Fin.last n)) (G.model.tailPoint side))
      (⟨0, by norm_num⟩ : BankJoinTime) occupied
      (fun s => s.val * ‖(G.model.bank side).direction‖) r) := by
  let R := G.model.bank side
  let p := R.chain.vertex (Fin.last (n + 1))
  let frame := if side then radialRightCornerFrame (p - R.start) R.direction
    else radialLeftCornerFrame (p - R.start) R.direction
  let F := bisectedSectorFan Real.pi Real.pi_pos (by linarith [Real.pi_pos])
  obtain ⟨r, rpos, A, center, physical⟩ := G.exists_model_straightJoin_chart side straight genuine
  have nonzero : R.direction ≠ 0 := straight.symm ▸ genuine (Fin.last n)
  have outward : R.Outward := by
    cases side
    · exact G.first_outward
    · exact G.second_outward
  have radial : 0 < inner ℝ (p - R.start) R.direction := by
    rw [straight]
    exact R.inner_terminal_edge_pos outward (Fin.last n)
      (fun eq => genuine _ (sub_eq_zero.mpr eq.symm))
  have radial_ne : p - R.start ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at radial
    exact (lt_irrefl _ radial)
  let B := halfTurnFanIsometry.trans (bankUpperNormalize side occupied)
  have model_center : B F.origin = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change bankAxisFrame side occupied (halfTurnFanIsometry F.origin).val = 0
    rw [halfTurnFanIsometry_val, F.develop_origin, map_zero]
  have joined_eq := joinedBank_zero (G.model.edgePoint side (Fin.last n)) (G.model.tailPoint side)
  let bank := joinedBank (G.model.edgePoint side (Fin.last n)) (G.model.tailPoint side)
  let zero : BankJoinTime := ⟨0, by norm_num⟩
  let move := basedEBallIsometry (IsometryEquiv.refl _) (bank zero) (G.model.tailPoint side 0)
    joined_eq (ENNReal.ofReal r)
  refine ⟨r, ⟨⟨rpos, (move.trans A).trans (basedEBallIsometry B _ _ model_center
    (ENNReal.ofReal r)), ?_, ?_⟩⟩⟩
  · have moved : move ⟨bank zero, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ =
        ⟨G.model.tailPoint side 0, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr rpos)⟩ :=
      Subtype.ext joined_eq
    change B (A (move _)).val = _
    rw [moved, center, model_center]
  · intro s near
    let y := move ⟨bank s, near⟩
    let u := if side then -s.val else s.val
    have pair : p + frame (F.develop (A y).val) = p + s.val • R.direction :=
      (physical y).trans (G.model.joinedBank_val side straight s)
    have coordinate : F.develop (A y).val = ((u * ‖R.direction‖ : ℝ) : ℂ) := by
      apply frame.injective
      apply add_left_cancel (a := p)
      refine pair.trans ?_
      cases side
      · change p + s.val • R.direction =
          p + radialLeftCornerFrame (p - R.start) R.direction ((s.val * ‖R.direction‖ : ℝ) : ℂ)
        rw [radialLeftCornerFrame_real_length _ _ radial_ne nonzero]
      · change p + s.val • R.direction =
          p + radialRightCornerFrame (p - R.start) R.direction ((-s.val * ‖R.direction‖ : ℝ) : ℂ)
        rw [radialRightCornerFrame_real_length _ _ radial_ne nonzero, neg_smul, smul_neg, neg_neg]
    change bankAxisFrame side occupied (halfTurnFanIsometry (A y).val).val = _
    rw [halfTurnFanIsometry_val, coordinate, bankAxisFrame_ofReal]
    cases side
    · rfl
    · apply congrArg Complex.ofReal
      change -(-s.val * ‖R.direction‖) = s.val * ‖R.direction‖
      rw [neg_mul, neg_neg]

end OrientedBankGap
end Unfoldings
