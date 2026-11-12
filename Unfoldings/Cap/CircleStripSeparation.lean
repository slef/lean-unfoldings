module

public import Unfoldings.Cap.StripCircleBanks

/-! Correctly ordered actual bank endpoints separate open developed strip-circle slices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.BankCircleSlice

variable {S T : MonotoneStrip} {G H : ℂ → ℂ} {center : ℂ} {a b radius : ℝ}

/-- Weak order across a cut gap permits boundary contact while keeping the two
open developed strip slices disjoint. Both intervals use their actual bank values. -/
theorem disjoint_circle_images_of_bank_order
    (first : S.BankCircleSlice G center a radius) (last : T.BankCircleSlice H center b radius)
    (first_order : (G (S.lower.point first.lowerHeight) - center).re <
      (G (S.upper.point first.upperHeight) - center).re)
    (last_order : (H (T.lower.point last.lowerHeight) - center).re <
      (H (T.upper.point last.upperHeight) - center).re)
    (gap_order : (G (S.upper.point first.upperHeight) - center).re ≤
      (H (T.lower.point last.lowerHeight) - center).re)
    (first_quadrant : ∀ z ∈ G '' S.openSlab 0 a,
      0 < (z - center).re ∧ 0 < (z - center).im) :
    Disjoint (G '' S.openSlab 0 a ∩ {z | ‖z - center‖ = radius})
      (H '' T.openSlab 0 b ∩ {z | ‖z - center‖ = radius}) := by
  have first_interval := first.interval
  rw [min_eq_left first_order.le, max_eq_right first_order.le] at first_interval
  have last_interval := last.interval
  rw [min_eq_left last_order.le, max_eq_right last_order.le] at last_interval
  apply Set.disjoint_left.mpr
  intro z in_first in_last
  have point := quadrantCirclePoint_eq_of_norm center
    ⟨(first_quadrant z in_first.1).1.le, (first_quadrant z in_first.1).2.le⟩ in_first.2
  have first_member : (z - center).re ∈
      quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 a) := by
    change quadrantCirclePoint center radius (z - center).re ∈ G '' S.openSlab 0 a
    rw [point]
    exact in_first.1
  have last_member : (z - center).re ∈
      quadrantCirclePoint center radius ⁻¹' (H '' T.openSlab 0 b) := by
    change quadrantCirclePoint center radius (z - center).re ∈ H '' T.openSlab 0 b
    rw [point]
    exact in_last.1
  rw [first_interval] at first_member
  rw [last_interval] at last_member
  exact (first_member.2.trans_le gap_order).not_ge last_member.1.le

end Unfoldings.MonotoneStrip.BankCircleSlice
