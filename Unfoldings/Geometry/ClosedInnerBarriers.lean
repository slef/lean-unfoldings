module

public import Unfoldings.Geometry.OrientedInnerBarriers

/-! Weak inner-barrier bounds identify the only possible contact of closed circle portions. -/

@[expose] public section

namespace Unfoldings

theorem quadrant_inner_barrier_cross_pos_of_norm_le_of_ne {x m : ℂ}
    (point : 0 ≤ x.re ∧ 0 < x.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ ≤ ‖x‖) (horizontal : x.re ≤ m.re) (different : x ≠ m) :
    0 < (starRingEnd ℂ m * x).im := by
  by_cases strict : x.re < m.re
  · exact quadrant_inner_barrier_cross_pos_of_norm_le point barrier outside strict
  · have real_eq : x.re = m.re := le_antisymm horizontal (not_lt.mp strict)
    have squares : m.re ^ 2 + m.im ^ 2 ≤ x.re ^ 2 + x.im ^ 2 := by
      have squared : ‖m‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg m, norm_nonneg x]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, Complex.normSq_apply] at squared
      simpa only [pow_two] using squared
    have imag_le : m.im ≤ x.im := by
      rw [real_eq] at squares
      nlinarith [point.2, barrier.2]
    have imag_ne : m.im ≠ x.im := fun equal => different (Complex.ext real_eq equal.symm)
    have vertical : m.im < x.im := lt_of_le_of_ne imag_le imag_ne
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    rw [real_eq]
    nlinarith [mul_pos barrier.1 (sub_pos.mpr vertical)]

theorem quadrant_inner_barrier_cross_neg_of_norm_le_of_ne {y m : ℂ}
    (point : 0 ≤ y.re ∧ 0 < y.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ ≤ ‖y‖) (vertical : y.im ≤ m.im) (different : y ≠ m) :
    (starRingEnd ℂ m * y).im < 0 := by
  by_cases strict : y.im < m.im
  · exact quadrant_inner_barrier_cross_neg_of_norm_le point barrier outside strict
  · have imag_eq : y.im = m.im := le_antisymm vertical (not_lt.mp strict)
    have squares : m.re ^ 2 + m.im ^ 2 ≤ y.re ^ 2 + y.im ^ 2 := by
      have squared : ‖m‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg m, norm_nonneg y]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, Complex.normSq_apply] at squared
      simpa only [pow_two] using squared
    have real_le : m.re ≤ y.re := by
      rw [imag_eq] at squares
      nlinarith [point.1, barrier.1]
    have real_ne : m.re ≠ y.re := fun equal => different (Complex.ext equal.symm imag_eq)
    have horizontal : m.re < y.re := lt_of_le_of_ne real_le real_ne
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    rw [imag_eq]
    nlinarith [mul_pos barrier.2 (sub_pos.mpr horizontal)]

theorem oriented_inner_barrier_point_eq_of_norm_le (F G : ℂ ≃ₗᵢ[ℝ] ℂ)
    (first_oriented : ∀ z w : ℂ, F (z * w) = z * F w)
    (last_oriented : ∀ z w : ℂ, G (z * w) = z * G w)
    {m z : ℂ} (first_barrier : 0 < (F m).re ∧ 0 < (F m).im)
    (last_barrier : 0 < (G m).re ∧ 0 < (G m).im)
    (first : 0 ≤ (F z).re ∧ 0 < (F z).im) (last : 0 ≤ (G z).re ∧ 0 < (G z).im)
    (horizontal : (F z).re ≤ (F m).re) (vertical : (G z).im ≤ (G m).im)
    (outside : ‖m‖ ≤ ‖z‖) : z = m := by
  by_contra different
  have above := quadrant_inner_barrier_cross_pos_of_norm_le_of_ne first first_barrier
    (by simpa only [F.norm_map] using outside) horizontal (F.injective.ne different)
  have below := quadrant_inner_barrier_cross_neg_of_norm_le_of_ne last last_barrier
    (by simpa only [G.norm_map] using outside) vertical (G.injective.ne different)
  rw [complex_cross_eq_of_commutes_mul F first_oriented] at above
  rw [complex_cross_eq_of_commutes_mul G last_oriented] at below
  exact (not_lt_of_ge above.le below).elim

end Unfoldings
