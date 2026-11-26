module

public import Unfoldings.Geometry.GnomonicRadialFrame
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The pole closure adds at most the planar area of its normal triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real MeasureTheory

private theorem abs_gnomonicAreaPrimitive_sub_le (p q r : ℝ) :
    |gnomonicAreaPrimitive p q - gnomonicAreaPrimitive p r| ≤ |q - r| := by
  have order {q r : ℝ} (lt : q < r) :
      0 ≤ gnomonicAreaPrimitive p r - gnomonicAreaPrimitive p q ∧
        gnomonicAreaPrimitive p r - gnomonicAreaPrimitive p q ≤ r - q := by
    have diff : Differentiable ℝ (gnomonicAreaPrimitive p) :=
      fun t => (hasDerivAt_gnomonicAreaPrimitive p t).differentiableAt
    obtain ⟨x, _, slope⟩ := exists_deriv_eq_slope (gnomonicAreaPrimitive p) lt
      diff.continuous.continuousOn diff.differentiableOn
    rw [(hasDerivAt_gnomonicAreaPrimitive p x).deriv] at slope
    have sqrt_le : 1 ≤ √(1 + p ^ 2 + x ^ 2) := by
      apply (sq_le_sq₀ zero_le_one (sqrt_nonneg _)).mp
      rw [sq_sqrt (by positivity)]
      nlinarith only [sq_nonneg p, sq_nonneg x]
    have den : (1 : ℝ) ≤ (√(1 + p ^ 2 + x ^ 2)) ^ 3 := by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one sqrt_le 3
    have hh : 0 < (√(1 + p ^ 2 + x ^ 2)) ^ 3 := zero_lt_one.trans_le den
    have low : 0 ≤ 1 / (√(1 + p ^ 2 + x ^ 2)) ^ 3 := by positivity
    have hi := (div_le_one hh).mpr den
    rw [slope] at low hi
    exact ⟨(by simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr lt)).mp low),
      (div_le_one (sub_pos.mpr lt)).mp hi⟩
  rcases lt_trichotomy q r with h | rfl | h
  · rw [abs_sub_comm, abs_sub_comm q r, abs_of_nonneg (order h).1,
      abs_of_nonneg (sub_nonneg.mpr h.le)]
    exact (order h).2
  · simp
  · rw [abs_of_nonneg (order h).1, abs_of_nonneg (sub_nonneg.mpr h.le)]
    exact (order h).2

private theorem primitive_integrable (m b x y : ℝ) :
    IntervalIntegrable (fun p => gnomonicAreaPrimitive p (m * p + b)) volume x y := by
  apply Continuous.intervalIntegrable
  unfold gnomonicAreaPrimitive
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  positivity

/-- The two transport integrals over an affine triangular slice differ by at
most its length times its maximum vertical width divided by two. -/
theorem abs_affine_hinge_change_sub_le {u v : ℝ} (ordered : u ≤ v)
    (m₁ b₁ m₂ b₂ : ℝ)
    (one_end : m₁ * u + b₁ = m₂ * u + b₂ ∨ m₁ * v + b₁ = m₂ * v + b₂) :
    |hingeAngleChange m₁ b₁ u v - hingeAngleChange m₂ b₂ u v| ≤
      |m₁ - m₂| * (v - u) ^ 2 / 2 := by
  let F (p : ℝ) := gnomonicAreaPrimitive p (m₁ * p + b₁)
  let G (p : ℝ) := gnomonicAreaPrimitive p (m₂ * p + b₂)
  have f : IntervalIntegrable F volume u v := primitive_integrable _ _ _ _
  have g : IntervalIntegrable G volume u v := primitive_integrable _ _ _ _
  simp only [hingeAngleChange, ← integral_gnomonicHingeAngle]
  change |(∫ p in u..v, F p) - (∫ p in u..v, G p)| ≤ _
  rw [← intervalIntegral.integral_sub f g]
  apply (intervalIntegral.abs_integral_le_integral_abs ordered).trans
  have finish (h : ℝ → ℝ) (h_int : IntervalIntegrable h volume u v)
      (bound : ∀ t ∈ Set.Icc u v, |F t - G t| ≤ h t)
      (eval : (∫ t in u..v, h t) = |m₁ - m₂| * (v - u) ^ 2 / 2) :
      (∫ t in u..v, |F t - G t|) ≤ |m₁ - m₂| * (v - u) ^ 2 / 2 := by
    rw [← eval]
    apply intervalIntegral.integral_mono_on ordered (f.sub g).abs h_int bound
  rcases one_end with left | right
  · let h (t : ℝ) := |m₁ - m₂| * (t - u)
    refine finish h (Continuous.intervalIntegrable (by dsimp [h]; fun_prop) _ _) (fun t ht => ?_) ?_
    · have row : m₁ * t + b₁ - (m₂ * t + b₂) = (m₁ - m₂) * (t - u) := by
        linear_combination left
      exact (abs_gnomonicAreaPrimitive_sub_le t _ _).trans_eq (by rw [row, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.1)])
    · unfold h
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ => u)
          (continuous_id.intervalIntegrable u v)
          (continuous_const.intervalIntegrable u v),
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
  · let h (t : ℝ) := |m₁ - m₂| * (v - t)
    refine finish h (Continuous.intervalIntegrable (by dsimp [h]; fun_prop) _ _) (fun t ht => ?_) ?_
    · have row : m₁ * t + b₁ - (m₂ * t + b₂) = (m₂ - m₁) * (v - t) := by
        linear_combination right
      exact (abs_gnomonicAreaPrimitive_sub_le t _ _).trans_eq (by
        rw [row, abs_mul, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)])
    · unfold h
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun _ => v) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable u v)
          (continuous_id.intervalIntegrable u v),
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring


private theorem hingeAngleChange_add (m b x y z : ℝ) :
    hingeAngleChange m b x y + hingeAngleChange m b y z = hingeAngleChange m b x z := by
  unfold hingeAngleChange
  ring

private theorem triangle_transport_nonnegative_last {p q r s m b : ℝ} (ordered : p < r) (rp : 0 < r)
    (first : m * p + b = q) (last : m * r + b = s) :
    |Cap.radialSectionHeading r s - Cap.radialSectionHeading p q - hingeAngleChange m b p r| ≤
      |p * s - r * q| / 2 := by
  let u := q / p
  let v := s / r
  let det := p * s - r * q
  have diff : 0 < r - p := sub_pos.mpr ordered
  have vs : v * r = s := div_mul_cancel₀ s rp.ne'
  have rv : Cap.radialSectionHeading r s = hingeAngleChange v 0 0 r := by
    rw [← vs, Cap.radialSectionHeading_eq_hingeAngleChange]
  have diff_v : m - v = det / (r * (r - p)) := by
    unfold det v
    field_simp [rp.ne', diff.ne']
    rw [← first, ← last]
    ring
  have pos_v : 0 < r * (r - p) := mul_pos rp diff
  by_cases pp : p = 0
  · subst p
    have h := abs_affine_hinge_change_sub_le rp.le v 0 m b (Or.inr (by simpa only [add_zero] using vs.trans last.symm))
    rw [rv, Cap.radialSectionHeading_zero, sub_zero]
    apply h.trans_eq
    change |v - m| * (r - 0) ^ 2 / 2 = |det| / 2
    rw [abs_sub_comm, diff_v, abs_div, abs_of_pos pos_v, sub_zero]
    field_simp [rp.ne']
    <;> ring
  · have us : u * p = q := div_mul_cancel₀ q pp
    have ru : Cap.radialSectionHeading p q = hingeAngleChange u 0 0 p := by
      rw [← us, Cap.radialSectionHeading_eq_hingeAngleChange]
    rw [rv, ru]
    rcases lt_or_gt_of_ne pp with neg | pos
    · have left := abs_affine_hinge_change_sub_le neg.le u 0 m b
        (Or.inl (by simpa only [add_zero] using us.trans first.symm))
      have right := abs_affine_hinge_change_sub_le rp.le v 0 m b
        (Or.inr (by simpa only [add_zero] using vs.trans last.symm))
      have loop :
          hingeAngleChange v 0 0 r - hingeAngleChange u 0 0 p - hingeAngleChange m b p r =
            (hingeAngleChange u 0 p 0 - hingeAngleChange m b p 0) +
              (hingeAngleChange v 0 0 r - hingeAngleChange m b 0 r) := by
        unfold hingeAngleChange
        ring
      rw [loop]
      apply (abs_add_le _ _).trans
      apply (add_le_add left right).trans_eq
      have diff_u : u - m = -det / (p * (r - p)) := by
        unfold det u
        field_simp [pp, diff.ne']
        rw [← first, ← last]
        ring
      rw [diff_u, abs_div, abs_neg, abs_of_neg (mul_neg_of_neg_of_pos neg diff),
        abs_sub_comm v m, diff_v, abs_div, abs_of_pos pos_v]
      field_simp [pp, rp.ne', diff.ne']
      <;> ring
    · have left := abs_affine_hinge_change_sub_le pos.le v 0 u 0
        (Or.inl (by simp))
      have right := abs_affine_hinge_change_sub_le ordered.le v 0 m b
        (Or.inr (by simpa only [add_zero] using vs.trans last.symm))
      have loop :
          hingeAngleChange v 0 0 r - hingeAngleChange u 0 0 p - hingeAngleChange m b p r =
            (hingeAngleChange v 0 0 p - hingeAngleChange u 0 0 p) +
              (hingeAngleChange v 0 p r - hingeAngleChange m b p r) := by
        unfold hingeAngleChange
        ring
      rw [loop]
      apply (abs_add_le _ _).trans
      apply (add_le_add left right).trans_eq
      have diff_uv : v - u = det / (p * r) := by
        unfold det u v
        field_simp [pp, rp.ne'] <;> ring
      rw [diff_uv, abs_div, abs_of_pos (mul_pos pos rp),
        abs_sub_comm v m, diff_v, abs_div, abs_of_pos pos_v]
      field_simp [pp, rp.ne', diff.ne']
      <;> ring

/-- The correction from closing the trace by the chord to closing it by both
pole radii has absolute value at most half the determinant of the two slopes. -/
theorem abs_radialSectionHeading_sub_hingeAngleChange_le {p q r s m b : ℝ} (ordered : p < r)
    (first : m * p + b = q) (last : m * r + b = s) :
    |Cap.radialSectionHeading r s - Cap.radialSectionHeading p q - hingeAngleChange m b p r| ≤
      |p * s - r * q| / 2 := by
  rcases lt_or_ge 0 r with rp | rn
  · exact triangle_transport_nonnegative_last ordered rp first last
  · have reflected := triangle_transport_nonnegative_last (neg_lt_neg ordered)
      (neg_pos.mpr (ordered.trans_le rn))
      (m := -m) (b := b) (q := s) (s := q)
      (by simpa only [neg_mul_neg] using last) (by simpa only [neg_mul_neg] using first)
    have refl_heading (x y : ℝ) :
        Cap.radialSectionHeading (-x) y = -Cap.radialSectionHeading x y := by
      unfold Cap.radialSectionHeading
      rw [neg_sq, neg_mul, neg_div, arctan_neg]
    have refl_hinge (x : ℝ) : gnomonicHingeRatio (-m) b (-x) = -gnomonicHingeRatio m b x := by
      unfold gnomonicHingeRatio
      rw [neg_sq, neg_mul_neg]
      ring
    have eq : hingeAngleChange (-m) b (-r) (-p) = hingeAngleChange m b p r := by
      unfold hingeAngleChange
      rw [refl_hinge, refl_hinge, arctan_neg, arctan_neg]
      ring
    rw [refl_heading, refl_heading, eq] at reflected
    convert reflected using 2 <;> ring

end Unfoldings
