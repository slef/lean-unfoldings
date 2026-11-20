module

public import Unfoldings.Geometry.AngleConeBound
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Soundness of the visual-angle pair tests used in the finite certificates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))

/-- Unsigned area is the product of the lengths times the sine of the
unoriented angle. -/
theorem abs_areaForm_eq_sin_angle (x y : E) :
    |o.areaForm x y| = sin (angle x y) * (‖x‖ * ‖y‖) := by
  have sine := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg x y) (angle_le_pi x y)
  apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg sine (by positivity))).mp
  have pythagoras := o.inner_sq_add_areaForm_sq x y
  rw [← cos_angle_mul_norm_mul_norm x y, mul_pow, mul_pow] at pythagoras
  rw [sq_abs, mul_pow, mul_pow]
  linear_combination pythagoras - (‖x‖ ^ 2 * ‖y‖ ^ 2) * sin_sq_add_cos_sq (angle x y)

/-- Negative signed polynomial at both endpoints certifies the whole side
interval. Either witness sign is represented by the sign of the coefficient. -/
def visualPairPolynomial (coefficient : ℝ) (p x y : E) : ℝ :=
  inner ℝ (p - x) (p - y) + coefficient * o.areaForm (p - x) (p - y)

theorem visualPairPolynomial_segment_lt_zero {c t : ℝ} {p q x y : E}
    (first : visualPairPolynomial o c p x y < 0)
    (last : visualPairPolynomial o c q x y < 0) (start : 0 ≤ t) (finish : t ≤ 1) :
    visualPairPolynomial o c (p + t • (q - p)) x y < 0 := by
  let d := q - p
  let slope := inner ℝ (p - x) d + inner ℝ d (p - y) +
    c * (o.areaForm (p - x) d + o.areaForm d (p - y))
  have expansion (s : ℝ) :
      visualPairPolynomial o c (p + s • d) x y =
        visualPairPolynomial o c p x y + s * slope + s ^ 2 * ‖d‖ ^ 2 := by
    unfold visualPairPolynomial
    rw [show p + s • d - x = (p - x) + s • d by abel,
      show p + s • d - y = (p - y) + s • d by abel]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, o.areaForm_apply_self d, slope]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have end_eq : p + (1 : ℝ) • d = q := by rw [one_smul]; dsimp [d]; abel
  have at_end := expansion 1
  rw [end_eq] at at_end
  have interpolation :
      visualPairPolynomial o c (p + t • d) x y =
        (1 - t) * visualPairPolynomial o c p x y + t * visualPairPolynomial o c q x y -
          t * (1 - t) * ‖d‖ ^ 2 := by
    rw [expansion t]
    linear_combination -t * at_end
  rw [interpolation]
  have error_nonneg := mul_nonneg (mul_nonneg start (sub_nonneg.mpr finish)) (sq_nonneg ‖d‖)
  have strict : (1 - t) * visualPairPolynomial o c p x y +
      t * visualPairPolynomial o c q x y < 0 := by
    by_cases ht : t = 0
    · simpa [ht] using first
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (by linarith) first.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne start (Ne.symm ht)) last)
  linarith

/-- A negative signed pair polynomial certifies a strict lower visual angle. -/
theorem visualAngle_lt_of_pair_polynomial {a c : ℝ} {p x y : E}
    (a_pos : 0 < a) (a_small : a ≤ π / 2) (cot_bound : |c| * sin a < cos a)
    (negative : visualPairPolynomial o c p x y < 0) :
    a < angle (p - x) (p - y) := by
  let u := p - x
  let v := p - y
  let α := angle u v
  have u_ne : u ≠ 0 := by
    intro zero
    change inner ℝ u v + c * o.areaForm u v < 0 at negative
    simp [zero] at negative
  have v_ne : v ≠ 0 := by
    intro zero
    change inner ℝ u v + c * o.areaForm u v < 0 at negative
    simp [zero] at negative
  have lengths := mul_pos (norm_pos_iff.mpr u_ne) (norm_pos_iff.mpr v_ne)
  by_contra not_less
  have ordered : α ≤ a := le_of_not_gt not_less
  have cosine := cos_le_cos_of_nonneg_of_le_pi (angle_nonneg u v)
    (by linarith [pi_pos]) ordered
  have sine := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos, angle_nonneg u v])
    a_small ordered
  have bound : c * o.areaForm u v ≥ -(|c| * (sin α * (‖u‖ * ‖v‖))) := by
    rw [← abs_areaForm_eq_sin_angle o, ← abs_mul]
    exact neg_abs_le _
  have inner_eq : inner ℝ u v = cos α * (‖u‖ * ‖v‖) :=
    (cos_angle_mul_norm_mul_norm _ _).symm
  have strict := lt_of_lt_of_le cot_bound cosine
  have scaled := mul_pos (sub_pos.mpr strict) lengths
  have sine_scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left sine (abs_nonneg c)) lengths.le
  change inner ℝ u v + c * o.areaForm u v < 0 at negative
  rw [inner_eq] at negative
  nlinarith

/-- A point outside the closed forbidden lens of a pair sees the pair under
an angle strictly below the paper's upper threshold. -/
theorem visualAngle_lt_supplement_of_outside_lens {a c : ℝ} {p x y : E}
    (a_pos : 0 < a) (a_small : a ≤ π / 2) (c_nonneg : 0 ≤ c)
    (cot_bound : c * sin a < cos a)
    (outside : 0 < inner ℝ (p - x) (p - y) + c * |o.areaForm (p - x) (p - y)|) :
    angle (p - x) (p - y) < π - a := by
  let u := p - x
  let v := p - y
  let α := angle u v
  change 0 < inner ℝ u v + c * |o.areaForm u v| at outside
  have u_ne : u ≠ 0 := by
    intro zero
    simp [zero] at outside
  have v_ne : v ≠ 0 := by
    intro zero
    simp [zero] at outside
  have lengths := mul_pos (norm_pos_iff.mpr u_ne) (norm_pos_iff.mpr v_ne)
  by_contra not_less
  have ordered : π - a ≤ α := le_of_not_gt not_less
  have supplementary : π - α ≤ a := by linarith
  have cosine := cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos])
    (angle_le_pi u v) ordered
  rw [cos_pi_sub] at cosine
  have sine := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos, angle_le_pi u v])
    a_small supplementary
  rw [sin_pi_sub] at sine
  rw [← cos_angle_mul_norm_mul_norm u v, abs_areaForm_eq_sin_angle o] at outside
  have coefficient : cos α + c * sin α < 0 := by
    have s := mul_le_mul_of_nonneg_left sine c_nonneg
    linarith
  have contradiction := mul_neg_of_neg_of_pos coefficient lengths
  nlinarith

end Unfoldings.FewestNets
