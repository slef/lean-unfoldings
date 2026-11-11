module

public import Unfoldings.Geometry.ComplexHingeTurn

/-! Positively oriented complex orthogonal frames commute with all rigid phase rotations. -/

@[expose] public section

namespace Unfoldings

theorem complex_cross_conj (x y : ℂ) :
    (starRingEnd ℂ (starRingEnd ℂ x) * starRingEnd ℂ y).im =
      -(starRingEnd ℂ x * y).im := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- One positive pair excludes conjugation in Mathlib's classification. -/
theorem complex_isometry_commutes_mul_of_cross (F : ℂ ≃ₗᵢ[ℝ] ℂ) (x y : ℂ)
    (positive : 0 < (starRingEnd ℂ x * y).im)
    (mapped : 0 ≤ (starRingEnd ℂ (F x) * F y).im) (z w : ℂ) : F (z * w) = z * F w := by
  obtain ⟨a, direct | conjugate⟩ := linear_isometry_complex F
  · rw [direct]
    simp only [rotation_apply]
    ring
  · have reverse : (starRingEnd ℂ (F x) * F y).im = -(starRingEnd ℂ x * y).im := by
      rw [conjugate]
      change (starRingEnd ℂ ((a : ℂ) * starRingEnd ℂ x) *
        ((a : ℂ) * starRingEnd ℂ y)).im = _
      rw [complex_cross_mul_unit _ _ _ (Circle.norm_coe a), complex_cross_conj]
    rw [reverse] at mapped
    exact (not_lt_of_ge mapped (neg_neg_of_pos positive)).elim

end Unfoldings
