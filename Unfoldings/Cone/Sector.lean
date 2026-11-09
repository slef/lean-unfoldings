module

public import Unfoldings.Cone.Polar
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Tactic.Ring

/-!
# Real-angle sectors and positive spans

Intermediate rays in a sector of width less than pi are positive combinations
of its boundary rays. The coefficients are strictly positive in the angular
interior. These identities connect real headings to actual convex wedges.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A real heading as its actual unit vector in the Euclidean complex plane. -/
def polarRay (θ : ℝ) : ℂ := Circle.exp θ

@[simp] theorem polarRay_re (θ : ℝ) : (polarRay θ).re = Real.cos θ := by
  exact Complex.exp_ofReal_mul_I_re θ

@[simp] theorem polarRay_im (θ : ℝ) : (polarRay θ).im = Real.sin θ := by
  exact Complex.exp_ofReal_mul_I_im θ

@[simp] theorem norm_polarRay (θ : ℝ) : ‖polarRay θ‖ = 1 := Circle.norm_coe _

@[simp] theorem polarRay_zero : polarRay 0 = 1 := by simp [polarRay]

theorem polarRay_add (a b : ℝ) : polarRay (a + b) = polarRay a * polarRay b := by
  exact congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_add a b)

theorem polarRay_ne_zero (θ : ℝ) : polarRay θ ≠ 0 := by
  have unit := norm_polarRay θ
  intro zero
  rw [zero, norm_zero] at unit
  exact zero_ne_one unit

theorem polarRay_div (a b : ℝ) : polarRay a / polarRay b = polarRay (a - b) := by
  simp only [polarRay, Circle.coe_exp, Complex.ofReal_sub, sub_mul, Complex.exp_sub]

/-- A sector narrower than a half-turn has its actual Euclidean angular width. -/
theorem angle_polarRay (a b : ℝ) (positive : 0 ≤ b - a) (small : b - a ≤ Real.pi) :
    InnerProductGeometry.angle (polarRay a) (polarRay b) = b - a := by
  rw [InnerProductGeometry.angle_comm,
    Complex.angle_eq_abs_arg (polarRay_ne_zero b) (polarRay_ne_zero a), polarRay_div]
  have argument : (polarRay (b - a)).arg = b - a :=
    Circle.arg_exp (by linarith [Real.pi_pos]) small
  rw [argument, abs_of_nonneg positive]

theorem polarRay_span_identity (a b θ : ℝ) :
    Real.sin (b - a) • polarRay θ =
      Real.sin (b - θ) • polarRay a + Real.sin (θ - a) • polarRay b := by
  apply Complex.ext <;>
    simp [polarRay, Circle.coe_exp, Complex.exp_mul_I, Real.sin_sub] <;> ring

theorem polarRay_combination (a b θ : ℝ) (nonzero : Real.sin (b - a) ≠ 0) :
    polarRay θ = (Real.sin (b - θ) / Real.sin (b - a)) • polarRay a +
      (Real.sin (θ - a) / Real.sin (b - a)) • polarRay b := by
  have identity := congrArg (fun z : ℂ => (Real.sin (b - a))⁻¹ • z)
    (polarRay_span_identity a b θ)
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul,
    div_eq_mul_inv, mul_comm] using identity

/-- Closed-sector directions belong to the positive span of its actual boundary vectors. -/
theorem polarRay_mem_positive_span (a b θ : ℝ)
    (positive : 0 < b - a) (small : b - a < Real.pi)
    (inside : θ ∈ Set.Icc a b) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ d : ℝ, 0 ≤ d ∧
      polarRay θ = c • polarRay a + d • polarRay b := by
  have denominator : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi positive small
  have left : 0 ≤ Real.sin (b - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr inside.2) (by linarith [inside.1])
  have right : 0 ≤ Real.sin (θ - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr inside.1) (by linarith [inside.2])
  exact ⟨Real.sin (b - θ) / Real.sin (b - a), div_nonneg left denominator.le,
    Real.sin (θ - a) / Real.sin (b - a), div_nonneg right denominator.le,
    polarRay_combination a b θ denominator.ne'⟩

/-- Strictly intermediate directions have both positive ray coefficients. -/
theorem polarRay_mem_strict_positive_span (a b θ : ℝ)
    (small : b - a < Real.pi) (inside : θ ∈ Set.Ioo a b) :
    ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧
      polarRay θ = c • polarRay a + d • polarRay b := by
  have denominator : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [inside.1, inside.2]) small
  have left : 0 < Real.sin (b - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr inside.2) (by linarith [inside.1])
  have right : 0 < Real.sin (θ - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr inside.1) (by linarith [inside.2])
  exact ⟨Real.sin (b - θ) / Real.sin (b - a), div_pos left denominator,
    Real.sin (θ - a) / Real.sin (b - a), div_pos right denominator,
    polarRay_combination a b θ denominator.ne'⟩

end Unfoldings
