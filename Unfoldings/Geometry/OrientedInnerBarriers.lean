module

public import Unfoldings.Geometry.QuadrantCircleOrderTransport

/-! A common inner point separates outward arcs measured in different oriented frames. -/

@[expose] public section

namespace Unfoldings

theorem quadrant_inner_barrier_cross_pos {x m : ℂ}
    (point : 0 ≤ x.re ∧ 0 < x.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ < ‖x‖) (horizontal : x.re ≤ m.re) :
    0 < (starRingEnd ℂ m * x).im := by
  have squares : m.re ^ 2 + m.im ^ 2 < x.re ^ 2 + x.im ^ 2 := by
    have squared : ‖m‖ ^ 2 < ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg m, norm_nonneg x]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply] at squared
    simpa only [pow_two] using squared
  have vertical : m.im < x.im := by
    by_contra below
    have reverse : x.im ≤ m.im := not_lt.mp below
    nlinarith [sq_nonneg (m.re - x.re), sq_nonneg (m.im - x.im)]
  have first := mul_le_mul_of_nonneg_right horizontal barrier.2.le
  have last := mul_lt_mul_of_pos_left vertical barrier.1
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem quadrant_inner_barrier_cross_neg {y m : ℂ}
    (point : 0 ≤ y.re ∧ 0 < y.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ < ‖y‖) (vertical : y.im ≤ m.im) :
    (starRingEnd ℂ m * y).im < 0 := by
  have squares : m.re ^ 2 + m.im ^ 2 < y.re ^ 2 + y.im ^ 2 := by
    have squared : ‖m‖ ^ 2 < ‖y‖ ^ 2 := by
      nlinarith [norm_nonneg m, norm_nonneg y]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply] at squared
    simpa only [pow_two] using squared
  have horizontal : m.re < y.re := by
    by_contra before
    have reverse : y.re ≤ m.re := not_lt.mp before
    nlinarith [sq_nonneg (m.re - y.re), sq_nonneg (m.im - y.im)]
  have first := mul_le_mul_of_nonneg_left vertical barrier.1.le
  have last := mul_lt_mul_of_pos_right horizontal barrier.2
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem quadrant_inner_barrier_cross_pos_of_norm_le {x m : ℂ}
    (point : 0 ≤ x.re ∧ 0 < x.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ ≤ ‖x‖) (horizontal : x.re < m.re) :
    0 < (starRingEnd ℂ m * x).im := by
  have squares : m.re ^ 2 + m.im ^ 2 ≤ x.re ^ 2 + x.im ^ 2 := by
    have squared : ‖m‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg m, norm_nonneg x]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply] at squared
    simpa only [pow_two] using squared
  have vertical : m.im < x.im := by
    by_contra below
    have reverse : x.im ≤ m.im := not_lt.mp below
    nlinarith [sq_nonneg (m.re - x.re), sq_nonneg (m.im - x.im)]
  have first := mul_le_mul_of_nonneg_right horizontal.le barrier.2.le
  have last := mul_lt_mul_of_pos_left vertical barrier.1
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem quadrant_inner_barrier_cross_neg_of_norm_le {y m : ℂ}
    (point : 0 ≤ y.re ∧ 0 < y.im) (barrier : 0 < m.re ∧ 0 < m.im)
    (outside : ‖m‖ ≤ ‖y‖) (vertical : y.im < m.im) :
    (starRingEnd ℂ m * y).im < 0 := by
  have squares : m.re ^ 2 + m.im ^ 2 ≤ y.re ^ 2 + y.im ^ 2 := by
    have squared : ‖m‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg m, norm_nonneg y]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply] at squared
    simpa only [pow_two] using squared
  have horizontal : m.re < y.re := by
    by_contra before
    have reverse : y.re ≤ m.re := not_lt.mp before
    nlinarith [sq_nonneg (m.re - y.re), sq_nonneg (m.im - y.im)]
  have first := mul_le_mul_of_nonneg_left vertical.le barrier.1.le
  have last := mul_lt_mul_of_pos_right horizontal barrier.2
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem oriented_inner_barrier_point_exclusion_of_norm_le (F G : ℂ ≃ₗᵢ[ℝ] ℂ)
    (first_oriented : ∀ z w : ℂ, F (z * w) = z * F w)
    (last_oriented : ∀ z w : ℂ, G (z * w) = z * G w)
    {m z : ℂ} (first_barrier : 0 < (F m).re ∧ 0 < (F m).im)
    (last_barrier : 0 < (G m).re ∧ 0 < (G m).im)
    (first : 0 ≤ (F z).re ∧ 0 < (F z).im) (last : 0 ≤ (G z).re ∧ 0 < (G z).im)
    (horizontal : (F z).re < (F m).re) (vertical : (G z).im < (G m).im)
    (outside : ‖m‖ ≤ ‖z‖) : False := by
  have above := quadrant_inner_barrier_cross_pos_of_norm_le first first_barrier
    (by simpa only [F.norm_map] using outside) horizontal
  have below := quadrant_inner_barrier_cross_neg_of_norm_le last last_barrier
    (by simpa only [G.norm_map] using outside) vertical
  rw [complex_cross_eq_of_commutes_mul F first_oriented] at above
  rw [complex_cross_eq_of_commutes_mul G last_oriented] at below
  exact (not_lt_of_ge above.le below).elim

theorem oriented_inner_barrier_point_exclusion (F G : ℂ ≃ₗᵢ[ℝ] ℂ)
    (first_oriented : ∀ z w : ℂ, F (z * w) = z * F w)
    (last_oriented : ∀ z w : ℂ, G (z * w) = z * G w)
    {m z : ℂ} (first_barrier : 0 < (F m).re ∧ 0 < (F m).im)
    (last_barrier : 0 < (G m).re ∧ 0 < (G m).im)
    (first : 0 ≤ (F z).re ∧ 0 < (F z).im) (last : 0 ≤ (G z).re ∧ 0 < (G z).im)
    (horizontal : (F z).re ≤ (F m).re) (vertical : (G z).im ≤ (G m).im)
    (outside : ‖m‖ < ‖z‖) : False := by
  have above := quadrant_inner_barrier_cross_pos first first_barrier
    (by simpa only [F.norm_map] using outside) horizontal
  have below := quadrant_inner_barrier_cross_neg last last_barrier
    (by simpa only [G.norm_map] using outside) vertical
  rw [complex_cross_eq_of_commutes_mul F first_oriented] at above
  rw [complex_cross_eq_of_commutes_mul G last_oriented] at below
  exact (not_lt_of_ge above.le below).elim

/-- The two coordinate tests may use different quadrant frames. Their
opposite signed areas are measured against the same actual inner point. -/
theorem oriented_inner_barrier_separates (F G : ℂ ≃ₗᵢ[ℝ] ℂ)
    (first_oriented : ∀ z w : ℂ, F (z * w) = z * F w)
    (last_oriented : ∀ z w : ℂ, G (z * w) = z * G w)
    {m : ℂ} (first_barrier : 0 < (F m).re ∧ 0 < (F m).im)
    (last_barrier : 0 < (G m).re ∧ 0 < (G m).im) {A B : Set ℂ}
    (first : ∀ z ∈ A, 0 ≤ (F z).re ∧ 0 < (F z).im ∧ (F z).re ≤ (F m).re)
    (last : ∀ z ∈ B, 0 ≤ (G z).re ∧ 0 < (G z).im ∧ (G z).im ≤ (G m).im)
    (first_outside : ∀ z ∈ A, ‖m‖ < ‖z‖)
    (last_outside : ∀ z ∈ B, ‖m‖ < ‖z‖) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro z member other_member
  have first_bounds := first z member
  have last_bounds := last z other_member
  have above := quadrant_inner_barrier_cross_pos ⟨first_bounds.1, first_bounds.2.1⟩
    first_barrier (by simpa only [F.norm_map] using first_outside z member) first_bounds.2.2
  have below := quadrant_inner_barrier_cross_neg ⟨last_bounds.1, last_bounds.2.1⟩
    last_barrier (by simpa only [G.norm_map] using last_outside z other_member) last_bounds.2.2
  rw [complex_cross_eq_of_commutes_mul F first_oriented] at above
  rw [complex_cross_eq_of_commutes_mul G last_oriented] at below
  exact (not_lt_of_ge above.le below).elim

end Unfoldings
