module

public import Unfoldings.Geometry.ComplexRotation
public import Mathlib.Tactic.FieldSimp

/-! An explicit stability estimate for normalized complex directions. -/

@[expose] public section

namespace Unfoldings

/-- Normalizing a nonzero vector costs at most twice its relative perturbation. -/
theorem complex_normalized_sub_le (x y : ℂ) (nonzero : x ≠ 0) (other : y ≠ 0) :
    ‖x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ)‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have nx := norm_pos_iff.mpr nonzero
  have ny := norm_pos_iff.mpr other
  have cx : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nx.ne'
  have cy : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ny.ne'
  have expression : x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ) =
      ((x - y) + ((‖y‖ - ‖x‖ : ℝ) : ℂ) * (y / (‖y‖ : ℂ))) / (‖x‖ : ℂ) := by
    push_cast
    field_simp
    ring
  have unit : ‖y / (‖y‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ny, div_self ny.ne']
  have error : ‖((‖y‖ - ‖x‖ : ℝ) : ℂ) * (y / (‖y‖ : ℂ))‖ ≤ ‖x - y‖ := by
    rw [norm_mul, unit, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_norm_sub_norm_le y x).trans_eq (norm_sub_rev y x)
  rw [expression, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos nx]
  apply div_le_div_of_nonneg_right _ nx.le
  exact (norm_add_le _ _).trans (by linarith)

end Unfoldings
