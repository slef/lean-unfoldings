module

public import Unfoldings.Cap.ClosedRadialBankTrace
public import Unfoldings.Geometry.RecoverableStripClosure
public import Unfoldings.Geometry.MonotoneStripLocalCircleCrossing

/-! Every approached positive-width bank point has a genuine interior source-circle slice. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable {S : MonotoneStrip} {G : ℂ → ℂ} {center : ℂ} {cutoff : ℝ}

theorem RadialBankTraces.circle_nonempty_at_closed_active_bank
    (radial : S.RadialBankTraces G center cutoff) (continuous : Continuous G)
    (H : MonotoneHeightGraph) (wall : H = S.lower ∨ H = S.upper) {h radius : ℝ}
    (height : h ∈ Set.Ioo 0 cutoff)
    (closed : H.point h ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff})
    (size : ‖G (H.point h) - center‖ = radius)
    (active : S.lower.coordinate h < S.upper.coordinate h) :
    (G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius}).Nonempty := by
  let U := Set.Ioo (0 : ℝ) cutoff ∩
    {k | S.lower.coordinate k < S.upper.coordinate k}
  have opened : IsOpen U := isOpen_Ioo.inter
    (isOpen_lt S.lower.continuous S.upper.continuous)
  obtain ⟨δ, positive, inside⟩ := Metric.isOpen_iff.mp opened h ⟨height, active⟩
  let a := h - δ / 2
  let b := h + δ / 2
  have before : a < h := by dsimp only [a]; linarith
  have after : h < b := by dsimp only [b]; linarith
  have all_inside : Set.Icc a b ⊆ U := by
    intro k member
    apply inside
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [a, b] at member
    constructor <;> linarith [member.1, member.2]
  have ainside := all_inside ⟨le_rfl, before.le.trans after.le⟩
  have binside := all_inside ⟨before.le.trans after.le, le_rfl⟩
  have bclosed := S.bank_points_mem_closure_of_width
    ⟨binside.1.1.le, binside.1.2.le⟩ binside.2
  have approached_b : H.point b ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff} := by
    rcases wall with rfl | rfl
    · exact bclosed.1
    · exact bclosed.2
  have first := radial.strict_before_closed_height continuous H wall ainside.1.1 before closed
  have last := radial.strict_before_closed_height continuous H wall height.1 after approached_b
  rw [size] at first last
  exact S.circle_image_nonempty_of_local_bank_crossing continuous center H wall
    (before.le.trans after.le) ainside.1.1 binside.1.2
    (fun k member => (all_inside member).2) first last

end Unfoldings.MonotoneStrip
