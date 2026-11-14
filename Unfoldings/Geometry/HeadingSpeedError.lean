module

public import Unfoldings.Geometry.HeadingChordError

/-! Heading and speed errors jointly control actual polygonal bank chords. -/

@[expose] public section

namespace Unfoldings

theorem norm_scaled_polarRay_sub_one_le (stretch angle : ℝ) (lower : 1 ≤ stretch) :
    ‖(stretch : ℂ) * polarRay angle - 1‖ ≤ (stretch - 1) + stretch * |angle| := by
  have positive : 0 ≤ stretch := le_trans zero_le_one lower
  have split : (stretch : ℂ) * polarRay angle - 1 =
      ((stretch - 1 : ℝ) : ℂ) + (stretch : ℂ) * (polarRay angle - 1) := by
    push_cast
    ring
  rw [split]
  calc
    _ ≤ ‖((stretch - 1 : ℝ) : ℂ)‖ + ‖(stretch : ℂ) * (polarRay angle - 1)‖ := norm_add_le _ _
    _ = (stretch - 1) + stretch * ‖polarRay angle - 1‖ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr lower), abs_of_nonneg positive]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (norm_polarRay_sub_one_le angle) positive)

namespace PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error stretch : Fin n → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)

include changed in
/-- The reference and developed links may have different lengths, bounded by one speed factor. -/
theorem heading_speed_chord_error {anchor S : ℝ} (lower : ∀ i, 1 ≤ stretch i)
    (upper : ∀ i, stretch i ≤ S) :
    ‖polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0)‖ ≤
      (S - 1) * P.projectedLength + S * ∑ i, |error i - anchor| * ‖P.edge i‖ := by
  have sum_equal : polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0) =
        ∑ i, ((stretch i : ℂ) * polarRay (error i - anchor) - 1) * P.edge i := by
    rw [← Q.sum_edge, ← P.sum_edge, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [changed]
    have phase : polarRay (-anchor) * polarRay (error i) = polarRay (error i - anchor) := by
      rw [← polarRay_add]
      congr 1
      ring
    calc
      _ = ((stretch i : ℂ) * (polarRay (-anchor) * polarRay (error i)) - 1) * P.edge i := by ring
      _ = _ := by rw [phase]
  rw [sum_equal]
  calc
    _ ≤ ∑ i, ‖((stretch i : ℂ) * polarRay (error i - anchor) - 1) * P.edge i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ((S - 1) + S * |error i - anchor|) * ‖P.edge i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_scaled_polarRay_sub_one_le _ _ (lower i)).trans
        (add_le_add (sub_le_sub_right (upper i) 1)
          (mul_le_mul_of_nonneg_right (upper i) (abs_nonneg _)))
    _ = _ := by
      simp only [projectedLength, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

include changed in
theorem heading_speed_length_bound {S : ℝ} (lower : ∀ i, 0 ≤ stretch i)
    (upper : ∀ i, stretch i ≤ S) : Q.projectedLength ≤ S * P.projectedLength := by
  rw [projectedLength, projectedLength, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [changed, norm_mul, norm_mul, norm_polarRay, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (lower i)]
  exact mul_le_mul_of_nonneg_right (upper i) (norm_nonneg _)

end PolygonalChain
end Unfoldings
