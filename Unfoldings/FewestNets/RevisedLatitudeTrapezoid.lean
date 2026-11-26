module

public import Unfoldings.FewestNets.RevisedLatitudeRows
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact integration of the latitude trapezoids and the improved sine sum. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real
open scoped BigOperators

/-- The trapezoidal approximation on an equally spaced colatitude strip differs
from the exact sine integral by the same factor on every strip. -/
theorem sine_trapezoid (x y : ℝ) (nonzero : sin y ≠ 0) :
    y * (sin x + sin (x + 2 * y)) =
      (y * cos y / sin y) * (cos x - cos (x + 2 * y)) := by
  have left : x = (x + y) - y := by ring
  have right : x + 2 * y = (x + y) + y := by ring
  have ls := (congrArg sin left).trans (sin_sub (x + y) y)
  have rs := (congrArg sin right).trans (sin_add (x + y) y)
  have lc := (congrArg cos left).trans (cos_sub (x + y) y)
  have rc := (congrArg cos right).trans (cos_add (x + y) y)
  rw [ls, rs, lc, rc]
  field_simp [nonzero]
  ring

private theorem sum_forward_differences (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f j - f (j + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sum_sine_trapezoids {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (∑ j ∈ Finset.range (stripCount a),
      (rowStep a / 2) * (sin (colatitude a j) + sin (colatitude a (j + 1)))) =
      2 * cos (AcuteLatitudeGrid.polarRadius a) * ((rowStep a / 2) *
        cos (rowStep a / 2) / sin (rowStep a / 2)) := by
  let y := rowStep a / 2
  have dy := rowStep_bounds positive small
  have yp : 0 < y := half_pos ((mul_pos (by norm_num) (radius_pos positive)).trans dy.1)
  have ypi : y < π := by
    dsimp [y]
    linarith only [dy.2, radius_lt small, pi_gt_d2]
  have next (j : ℕ) : colatitude a (j + 1) = colatitude a j + 2 * y := by
    simp only [colatitude, Nat.cast_add, Nat.cast_one, y]
    ring
  calc
    _ = ∑ j ∈ Finset.range (stripCount a),
        (y * cos y / sin y) * (cos (colatitude a j) - cos (colatitude a (j + 1))) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [next]
      exact sine_trapezoid _ _ (sin_pos_of_pos_of_lt_pi yp ypi).ne'
    _ = _ := by
      rw [← Finset.mul_sum, sum_forward_differences, colatitude_last positive small, cos_pi_sub]
      simp only [colatitude, Nat.cast_zero, zero_mul, add_zero]
      ring

/-- Sharp enough near zero to retain the first-order contraction in the count. -/
theorem sine_sub_mul_cos_lower {y : ℝ} (hy : 0 ≤ y) :
    y ^ 3 / 3 - y ^ 5 / 30 ≤ sin y - y * cos y := by
  let lower (t : ℝ) := t ^ 2 - t ^ 4 / 6
  let density (t : ℝ) := t * sin t
  have lower_cont : Continuous lower := by fun_prop
  have density_cont : Continuous density := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy
    (lower_cont.intervalIntegrable 0 y) (density_cont.intervalIntegrable 0 y)
    (fun t ht => by
      have bound := mul_le_mul_of_nonneg_left (sin_ge_sub_cube ht.1) ht.1
      change lower t ≤ density t
      dsimp only [lower, density]
      linear_combination bound)
  have integrate_lower : (∫ t in (0 : ℝ)..y, lower t) = y ^ 3 / 3 - y ^ 5 / 30 := by
    unfold lower
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, integral_pow, integral_pow]
    · norm_num
      ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  have integrate_density : (∫ t in (0 : ℝ)..y, density t) = sin y - y * cos y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => sin t - t * cos t) (fun t _ => ?_) (density_cont.intervalIntegrable 0 y)]
    · simp
    · have deriv := (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t))
      convert deriv using 1 <;> try rfl
      simp only [density, id_eq]
      ring
  rwa [integrate_lower, integrate_density] at comparison

theorem cotangent_factor_bound {y : ℝ} (positive : 0 < y) (small : y < 0.261) :
    y * cos y / sin y ≤ 1 - 0.331 * y ^ 2 := by
  have sine_pos := sin_pos_of_pos_of_lt_pi positive (by linarith only [small, pi_gt_d2])
  have square := pow_le_pow_left₀ positive.le small.le 2
  have cube : 0 ≤ y ^ 3 := by positivity
  have fifth : y ^ 5 ≤ (0.261 : ℝ) ^ 2 * y ^ 3 := by
    rw [show y ^ 5 = y ^ 2 * y ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right square cube
  have difference : 0.331 * y ^ 3 ≤ sin y - y * cos y :=
    (show 0.331 * y ^ 3 ≤ y ^ 3 / 3 - y ^ 5 / 30 by linarith only [fifth, cube]).trans
      (sine_sub_mul_cos_lower positive.le)
  have error := mul_le_mul_of_nonneg_left (sin_le positive.le)
    (show 0 ≤ 0.331 * y ^ 2 by positivity)
  apply (div_le_iff₀ sine_pos).mpr
  nlinarith only [difference, error]

/-- The small polar radius gives a quantitative cosine deficit. -/
theorem polar_cosine_bound {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    cos (AcuteLatitudeGrid.polarRadius a) ≤ 1 - 0.49 * a / 144 := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  have rad : 0 < ρ := AcuteLatitudeGrid.polarRadius_pos positive
  have y_bound : ρ / 2 ≤ 0.031 := by
    linarith only [AcuteLatitudeGrid.polarRadius_lt small]
  have sq := pow_le_pow_left₀ (half_pos rad).le y_bound 2
  have err : (ρ / 2) ^ 3 / 6 ≤ 0.01 * (ρ / 2) := by
    calc
      _ = (ρ / 2) ^ 2 / 6 * (ρ / 2) := by ring
      _ ≤ 0.01 * (ρ / 2) := mul_le_mul_of_nonneg_right
        (by linarith only [sq]) (half_pos rad).le
  have sine : 0.99 * (ρ / 2) ≤ sin (ρ / 2) := by
    linarith only [err, sin_ge_sub_cube (half_pos rad).le]
  have square := pow_le_pow_left₀ (show 0 ≤ 0.99 * (ρ / 2) by positivity) sine 2
  have rad_square : ρ ^ 2 = a / 144 := by
    dsimp [ρ, AcuteLatitudeGrid.polarRadius]
    rw [div_pow, sq_sqrt positive.le]
    norm_num
  have expansion : cos ρ = 1 - 2 * sin (ρ / 2) ^ 2 := by
    calc
      _ = cos (2 * (ρ / 2)) := by congr 1; ring
      _ = _ := by
        rw [cos_two_mul]
        linarith only [sin_sq_add_cos_sq (ρ / 2)]
  rw [expansion]
  nlinarith only [square, rad_square, sq_nonneg ρ]

/-- The sum of row sines, counted twice on interior rows and once at each pole,
with the strict first-order improvement supplied by the exact trapezoids. -/
theorem weighted_sine_sum_bound {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (∑ j ∈ Finset.range (stripCount a),
      (rowStep a / 2) * (sin (colatitude a j) + sin (colatitude a (j + 1)))) ≤
      2 * (1 - 0.034 * a) := by
  let ρ := AcuteLatitudeGrid.polarRadius a
  let y := rowStep a / 2
  have step := rowStep_bounds positive small
  have yp : 0 < y := half_pos ((mul_pos (by norm_num) (radius_pos positive)).trans step.1)
  have ymax : y < 0.261 := by dsimp [y]; linarith only [step.2, radius_lt small]
  have lower : 0.30672 * √a ≤ y := by
    unfold radius at step
    dsimp [y]
    linarith only [step.1]
  have square := pow_le_pow_left₀
    (show 0 ≤ 0.30672 * √a by positivity) lower 2
  rw [mul_pow, sq_sqrt positive.le] at square
  have cot_bound : y * cos y / sin y ≤ 1 - 0.031 * a := by
    refine (cotangent_factor_bound yp ymax).trans ?_
    linarith only [square, positive]
  have rad_nonneg := (AcuteLatitudeGrid.polarRadius_pos positive).le
  have cos_nonneg : 0 ≤ cos ρ := by
    apply (cos_pos_of_mem_Ioo ⟨by linarith only [rad_nonneg, pi_gt_d2], ?_⟩).le
    linarith only [AcuteLatitudeGrid.polarRadius_lt small, pi_gt_d2]
  have amax : a ≤ 1 := by linarith only [small, pi_lt_d6]
  have cot_nonneg : 0 ≤ 1 - 0.031 * a := by linarith only [amax]
  rw [sum_sine_trapezoids positive small]
  change 2 * cos ρ * (y * cos y / sin y) ≤ _
  calc
    _ ≤ 2 * (cos ρ * (1 - 0.031 * a)) := by
      rw [mul_assoc]
      gcongr
    _ ≤ 2 * ((1 - 0.49 * a / 144) * (1 - 0.031 * a)) := by
      gcongr
      exact polar_cosine_bound positive small
    _ ≤ _ := by
      have sq_le : a ^ 2 ≤ a := by
        simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right amax positive.le
      nlinarith only [sq_le, positive]

end Unfoldings.FewestNets.RevisedLatitudeGrid
