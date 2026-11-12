module

public import Unfoldings.Cap.CircleStripSeparation
public import Unfoldings.Geometry.BankRadialOrder

/-! Open strip-circle points satisfy strict bounds at their actual approached banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.BankCircleSlice

variable {S : MonotoneStrip} {G : ℂ → ℂ} {center : ℂ} {cutoff radius : ℝ}
  (slice : S.BankCircleSlice G center cutoff radius)
  (ordered : (G (S.lower.point slice.lowerHeight) - center).re <
    (G (S.upper.point slice.upperHeight) - center).re)

include ordered

theorem re_bounds_of_mem_circle_image {z : ℂ}
    (quadrant : 0 ≤ (z - center).re ∧ 0 ≤ (z - center).im)
    (member : z ∈ G '' S.openSlab 0 cutoff ∩ {w | ‖w - center‖ = radius}) :
    (G (S.lower.point slice.lowerHeight) - center).re < (z - center).re ∧
      (z - center).re < (G (S.upper.point slice.upperHeight) - center).re := by
  have point := quadrantCirclePoint_eq_of_norm center quadrant member.2
  have inside : (z - center).re ∈
      quadrantCirclePoint center radius ⁻¹' (G '' S.openSlab 0 cutoff) := by
    change quadrantCirclePoint center radius (z - center).re ∈ G '' S.openSlab 0 cutoff
    rw [point]
    exact member.1
  have interval := slice.interval
  rw [min_eq_left ordered.le, max_eq_right ordered.le] at interval
  rwa [interval] at inside

theorem im_lt_lower_of_mem_circle_image
    (lower_quadrant : 0 ≤ (G (S.lower.point slice.lowerHeight) - center).re ∧
      0 ≤ (G (S.lower.point slice.lowerHeight) - center).im) {z : ℂ}
    (quadrant : 0 ≤ (z - center).re ∧ 0 ≤ (z - center).im)
    (member : z ∈ G '' S.openSlab 0 cutoff ∩ {w | ‖w - center‖ = radius}) :
    (z - center).im < (G (S.lower.point slice.lowerHeight) - center).im := by
  have horizontal := (slice.re_bounds_of_mem_circle_image ordered quadrant member).1
  have same := slice.lower_radius.trans member.2.symm
  have squared := congrArg (fun x : ℝ => x ^ 2) same
  have identity (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [identity, identity] at squared
  have real_square := mul_self_lt_mul_self lower_quadrant.1 horizontal
  by_contra vertical
  have imaginary_square := mul_self_le_mul_self lower_quadrant.2 (not_lt.mp vertical)
  nlinarith

end Unfoldings.MonotoneStrip.BankCircleSlice
