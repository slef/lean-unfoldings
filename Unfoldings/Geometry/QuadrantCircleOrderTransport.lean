module

public import Unfoldings.Geometry.BankRadialOrder
public import Unfoldings.Geometry.ComplexRotationFrame

/-! Circle endpoint order is independent of an oriented quadrant frame on their common domain. -/

@[expose] public section

namespace Unfoldings

theorem quadrant_circle_re_order_iff_cross_nonpos {x y : ℂ}
    (first : 0 ≤ x.re ∧ 0 ≤ x.im) (last : 0 ≤ y.re ∧ 0 ≤ y.im)
    (radius : ‖x‖ = ‖y‖) :
    x.re ≤ y.re ↔ (starRingEnd ℂ x * y).im ≤ 0 := by
  have squares : x.re ^ 2 + x.im ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    have same := congrArg (fun a : ℝ => a ^ 2) radius
    have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [identity x, identity y] at same
    exact same
  constructor
  · intro ordered
    have vertical := (quadrant_circle_order first.1 first.2 last.1 last.2 squares
      (Or.inl ordered)).2
    have product := mul_le_mul ordered vertical last.2 last.1
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    nlinarith
  · intro cross
    have alternative : x.re ≤ y.re ∨ y.im ≤ x.im := by
      by_cases ordered : x.re ≤ y.re
      · exact Or.inl ordered
      · right
        by_contra vertical
        have horizontal : y.re < x.re := not_le.mp ordered
        have above : x.im < y.im := not_le.mp vertical
        have product : y.re * x.im < x.re * y.im :=
          (mul_le_mul_of_nonneg_right horizontal.le first.2).trans_lt
            (mul_lt_mul_of_pos_left above (last.1.trans_lt horizontal))
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at cross
        nlinarith
    exact (quadrant_circle_order first.1 first.2 last.1 last.2 squares alternative).1

theorem complex_cross_eq_of_commutes_mul (F : ℂ ≃ₗᵢ[ℝ] ℂ)
    (commutes : ∀ z w : ℂ, F (z * w) = z * F w) (x y : ℂ) :
    (starRingEnd ℂ (F x) * F y).im = (starRingEnd ℂ x * y).im := by
  have rotation (z : ℂ) : F z = F 1 * z := by
    simpa only [mul_one, mul_comm] using commutes z 1
  rw [rotation x, rotation y]
  exact complex_cross_mul_unit (F 1) x y (by rw [F.norm_map, norm_one])

/-- Both endpoint pairs remain in their respective closed quadrants. No
assumption about the intervening strip or its other sector points is required. -/
theorem quadrant_circle_re_order_transport (F : ℂ ≃ₗᵢ[ℝ] ℂ)
    (commutes : ∀ z w : ℂ, F (z * w) = z * F w) {x y : ℂ}
    (first : 0 ≤ x.re ∧ 0 ≤ x.im) (last : 0 ≤ y.re ∧ 0 ≤ y.im)
    (mapped_first : 0 ≤ (F x).re ∧ 0 ≤ (F x).im)
    (mapped_last : 0 ≤ (F y).re ∧ 0 ≤ (F y).im)
    (radius : ‖x‖ = ‖y‖) : x.re ≤ y.re ↔ (F x).re ≤ (F y).re := by
  rw [quadrant_circle_re_order_iff_cross_nonpos first last radius,
    quadrant_circle_re_order_iff_cross_nonpos mapped_first mapped_last
      (by simpa only [F.norm_map] using radius),
    complex_cross_eq_of_commutes_mul F commutes]

end Unfoldings
