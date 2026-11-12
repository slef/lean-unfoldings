module

public import Unfoldings.Geometry.FiveSectorCycle
public import Unfoldings.Geometry.FiveSectorFrames
public import Unfoldings.Geometry.AcuteWedgeMarginAngle

/-! Exact cyclic offsets for the five overlapping comparison quadrants. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {t : ℝ} (positive : 0 < t) (small : t < 1)

theorem fiveSectorAngularFan_angle_eq (k : Fin 5) :
    (fiveSectorAngularFan t positive small).angle k = Real.pi / 2 -
      2 * (fiveSectorFrame t positive small (fiveSectorCycle k)).margin :=
  (fiveSectorFrame t positive small (fiveSectorCycle k)).angle_eq_pi_div_two_sub_two_margin

theorem sum_fiveSectorFrame_margin :
    (∑ k : Fin 5, (fiveSectorFrame t positive small (fiveSectorCycle k)).margin) = Real.pi / 4 := by
  have total := fiveSectorAngularFan_totalAngle positive small
  change (∑ k : Fin 5, (fiveSectorAngularFan t positive small).angle k) = 2 * Real.pi at total
  simp_rw [fiveSectorAngularFan_angle_eq positive small] at total
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at total
  linarith

/-- Subtracting the local margin from the physical first-ray heading gives
the unreduced start of the corresponding open comparison quadrant. -/
def fiveSectorQuadrantStart (k : Fin 5) : ℝ :=
  (fiveSectorAngularFan t positive small).heading k.castSucc -
    (fiveSectorFrame t positive small (fiveSectorCycle k)).margin

theorem fiveSectorQuadrantStart_succ (k : Fin 4) :
    fiveSectorQuadrantStart positive small k.succ =
      fiveSectorQuadrantStart positive small k.castSucc + Real.pi / 2 -
        (fiveSectorFrame t positive small (fiveSectorCycle k.castSucc)).margin -
        (fiveSectorFrame t positive small (fiveSectorCycle k.succ)).margin := by
  let A := fiveSectorAngularFan t positive small
  have step : A.heading k.succ.castSucc = A.heading k.castSucc.castSucc + A.angle k.castSucc :=
    A.heading_succ k.castSucc
  dsimp only [fiveSectorQuadrantStart]
  rw [step, fiveSectorAngularFan_angle_eq positive small]
  ring

theorem fiveSectorQuadrantStart_wrap :
    fiveSectorQuadrantStart positive small 0 + 2 * Real.pi =
      fiveSectorQuadrantStart positive small (Fin.last 4) + Real.pi / 2 -
        (fiveSectorFrame t positive small (fiveSectorCycle (Fin.last 4))).margin -
        (fiveSectorFrame t positive small (fiveSectorCycle 0)).margin := by
  let A := fiveSectorAngularFan t positive small
  have last := A.heading_succ (Fin.last 4)
  change A.heading (Fin.last 5) = A.heading (Fin.last 4).castSucc + A.angle (Fin.last 4) at last
  rw [A.heading_last, fiveSectorAngularFan_totalAngle positive small,
    fiveSectorAngularFan_angle_eq positive small] at last
  dsimp only [fiveSectorQuadrantStart]
  rw [Fin.castSucc_zero, AngularFan.heading_zero]
  linarith

theorem fiveSectorQuadrantStart_strictMono :
    StrictMono (fiveSectorQuadrantStart positive small) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  have first :=
    (fiveSectorFrame t positive small (fiveSectorCycle k.castSucc)).margin_lt_pi_div_four
    (fiveSector_banks_orient_pos positive small (fiveSectorCycle k.castSucc))
  have last := (fiveSectorFrame t positive small (fiveSectorCycle k.succ)).margin_lt_pi_div_four
    (fiveSector_banks_orient_pos positive small (fiveSectorCycle k.succ))
  rw [fiveSectorQuadrantStart_succ positive small]
  linarith

theorem fiveSectorQuadrantStart_two_step (k : Fin 3) :
    fiveSectorQuadrantStart positive small k.succ.succ =
      fiveSectorQuadrantStart positive small k.castSucc.castSucc + Real.pi -
        (fiveSectorFrame t positive small (fiveSectorCycle k.castSucc.castSucc)).margin -
        2 * (fiveSectorFrame t positive small (fiveSectorCycle k.succ.castSucc)).margin -
        (fiveSectorFrame t positive small (fiveSectorCycle k.succ.succ)).margin := by
  have first := fiveSectorQuadrantStart_succ positive small k.castSucc
  have last := fiveSectorQuadrantStart_succ positive small k.succ
  have middle : k.castSucc.succ = k.succ.castSucc := Fin.ext rfl
  rw [middle] at first
  linarith

/-- Nonadjacent comparison quadrants start more than a quarter turn apart,
but less than a half turn apart. The statement uses unreduced cyclic headings. -/
theorem fiveSectorQuadrantStart_two_apart (k : Fin 3) :
    Real.pi / 2 < fiveSectorQuadrantStart positive small k.succ.succ -
        fiveSectorQuadrantStart positive small k.castSucc.castSucc ∧
      fiveSectorQuadrantStart positive small k.succ.succ -
        fiveSectorQuadrantStart positive small k.castSucc.castSucc < Real.pi := by
  let δ := fun k : Fin 5 => (fiveSectorFrame t positive small (fiveSectorCycle k)).margin
  have total : δ 0 + δ 1 + δ 2 + δ 3 + δ 4 = Real.pi / 4 := by
    have sum := sum_fiveSectorFrame_margin positive small
    change (∑ k : Fin 5, δ k) = Real.pi / 4 at sum
    norm_num [Fin.sum_univ_succ] at sum
    linarith [sum]
  have positive_margin (j : Fin 5) : 0 < δ j :=
    (fiveSectorFrame t positive small (fiveSectorCycle j)).positive
  have step := fiveSectorQuadrantStart_two_step positive small k
  fin_cases k
  · change fiveSectorQuadrantStart positive small 2 =
      fiveSectorQuadrantStart positive small 0 + Real.pi - δ 0 -
        2 * δ 1 - δ 2 at step
    change Real.pi / 2 < fiveSectorQuadrantStart positive small 2 -
        fiveSectorQuadrantStart positive small 0 ∧
      fiveSectorQuadrantStart positive small 2 -
        fiveSectorQuadrantStart positive small 0 < Real.pi
    constructor <;> linarith [positive_margin 0, positive_margin 1, positive_margin 2,
      positive_margin 3, positive_margin 4]
  · change fiveSectorQuadrantStart positive small 3 =
      fiveSectorQuadrantStart positive small 1 + Real.pi - δ 1 -
        2 * δ 2 - δ 3 at step
    change Real.pi / 2 < fiveSectorQuadrantStart positive small 3 -
        fiveSectorQuadrantStart positive small 1 ∧
      fiveSectorQuadrantStart positive small 3 -
        fiveSectorQuadrantStart positive small 1 < Real.pi
    constructor <;> linarith [positive_margin 0, positive_margin 1, positive_margin 2,
      positive_margin 3, positive_margin 4]
  · change fiveSectorQuadrantStart positive small 4 =
      fiveSectorQuadrantStart positive small 2 + Real.pi - δ 2 -
        2 * δ 3 - δ 4 at step
    change Real.pi / 2 < fiveSectorQuadrantStart positive small 4 -
        fiveSectorQuadrantStart positive small 2 ∧
      fiveSectorQuadrantStart positive small 4 -
        fiveSectorQuadrantStart positive small 2 < Real.pi
    constructor <;> linarith [positive_margin 0, positive_margin 1, positive_margin 2,
      positive_margin 3, positive_margin 4]

/-- The two remaining nonadjacent pairs cross the chosen argument seam. -/
theorem fiveSectorQuadrantStart_wrap_two_apart :
    (Real.pi / 2 < fiveSectorQuadrantStart positive small 0 + 2 * Real.pi -
        fiveSectorQuadrantStart positive small 3 ∧
      fiveSectorQuadrantStart positive small 0 + 2 * Real.pi -
        fiveSectorQuadrantStart positive small 3 < Real.pi) ∧
    (Real.pi / 2 < fiveSectorQuadrantStart positive small 1 + 2 * Real.pi -
        fiveSectorQuadrantStart positive small 4 ∧
      fiveSectorQuadrantStart positive small 1 + 2 * Real.pi -
        fiveSectorQuadrantStart positive small 4 < Real.pi) := by
  let δ := fun k : Fin 5 => (fiveSectorFrame t positive small (fiveSectorCycle k)).margin
  have total : δ 0 + δ 1 + δ 2 + δ 3 + δ 4 = Real.pi / 4 := by
    have sum := sum_fiveSectorFrame_margin positive small
    change (∑ k : Fin 5, δ k) = Real.pi / 4 at sum
    norm_num [Fin.sum_univ_succ] at sum
    linarith [sum]
  have positive_margin (j : Fin 5) : 0 < δ j :=
    (fiveSectorFrame t positive small (fiveSectorCycle j)).positive
  have wrap := fiveSectorQuadrantStart_wrap positive small
  change fiveSectorQuadrantStart positive small 0 + 2 * Real.pi =
    fiveSectorQuadrantStart positive small 4 + Real.pi / 2 - δ 4 - δ 0 at wrap
  have last := fiveSectorQuadrantStart_succ positive small (3 : Fin 4)
  change fiveSectorQuadrantStart positive small 4 =
    fiveSectorQuadrantStart positive small 3 + Real.pi / 2 - δ 3 - δ 4 at last
  have first := fiveSectorQuadrantStart_succ positive small (0 : Fin 4)
  change fiveSectorQuadrantStart positive small 1 =
    fiveSectorQuadrantStart positive small 0 + Real.pi / 2 - δ 0 - δ 1 at first
  constructor <;> constructor <;>
    linarith [positive_margin 0, positive_margin 1, positive_margin 2,
      positive_margin 3, positive_margin 4]

end Unfoldings
