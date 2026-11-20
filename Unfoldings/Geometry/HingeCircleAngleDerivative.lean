module

public import Unfoldings.Geometry.HingeCircleSpeed
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Local angle derivatives of moving contacts on a fixed circle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped Topology RealInnerProductSpace

attribute [local instance] Complex.finrank_real_complex_fact

private theorem im_div_eq_areaForm_div_norm_sq (z p : ℂ) :
    (z / p).im = Complex.orientation.areaForm p z / ‖p‖ ^ 2 := by
  rw [Complex.div_im, Complex.areaForm, Complex.sq_norm, ← sub_div]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- At a constant-radius contact, measure the local angle relative to the
contact at time `t`. Its derivative is the oriented area rate divided by
the squared radius. -/
theorem hasDerivAt_circleContact_angle {f : ℝ → ℂ} {t : ℝ} {w : ℂ}
    (derivative : HasDerivAt f w t) (nonzero : f t ≠ 0)
    (constant_radius : ∀ᶠ x in 𝓝 t, ‖f x‖ = ‖f t‖) :
    HasDerivAt (fun x => Complex.arg (f x / f t))
      (Complex.orientation.areaForm (f t) w / ‖f t‖ ^ 2) t := by
  let p := f t
  let g (x : ℝ) := (f x / p).im
  let l : ℂ →L[ℝ] ℝ :=
    (‖p‖ ^ 2)⁻¹ • (Complex.orientation.areaForm p).toContinuousLinearMap
  have eval (z : ℂ) : l z = (z / p).im := by
    rw [im_div_eq_areaForm_div_norm_sq]
    change (‖p‖ ^ 2)⁻¹ * Complex.orientation.areaForm p z = _
    ring
  have hg : HasDerivAt g (l w) t := by
    have h := l.hasFDerivAt.comp_hasDerivAt t derivative
    simpa only [Function.comp_def, eval, g] using h
  have zero : g t = 0 := by simp [g, p, nonzero]
  have arcsin : HasDerivAt Real.arcsin 1 (g t) := by
    rw [zero]
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have angle : HasDerivAt (fun x => Real.arcsin (g x)) (l w) t := by
    simpa only [Function.comp_def, one_mul] using arcsin.comp t hg
  have continuous : ContinuousAt (fun x => (f x / p).re) t :=
    Complex.continuous_re.continuousAt.comp (derivative.continuousAt.div_const p)
  have re_pos : ∀ᶠ x in 𝓝 t, 0 < (f x / p).re := by
    have ht : 0 < (f t / p).re := by simp [p, nonzero]
    exact continuous (Ioi_mem_nhds ht)
  have same : (fun x => Complex.arg (f x / p)) =ᶠ[𝓝 t] fun x => Real.arcsin (g x) := by
    filter_upwards [constant_radius, re_pos] with x radius re
    rw [Complex.arg_of_re_nonneg re.le, norm_div, radius,
      div_self (norm_ne_zero_iff.mpr nonzero), div_one]
  have result := angle.congr_of_eventuallyEq same
  have at_w : l w = Complex.orientation.areaForm p w / ‖p‖ ^ 2 :=
    (eval w).trans (im_div_eq_areaForm_div_norm_sq w p)
  rwa [at_w] at result

/-- The rate bound applies to the actual angle derivative of a differentiable
fixed-radius contact, once rotation and sliding describe its velocity. -/
theorem circleContact_angle_derivative_le {f : ℝ → ℂ} {t : ℝ} {w h v : ℂ} {m slide : ℝ}
    (derivative : HasDerivAt f w t) (nonzero : f t ≠ 0)
    (constant_radius : ∀ᶠ x in 𝓝 t, ‖f x‖ = ‖f t‖)
    (m_pos : 0 < m) (v_ne : v ≠ 0) (hinge : ‖h‖ ≤ ‖f t‖)
    (margin : m * (‖f t‖ * ‖v‖) ≤ inner ℝ (f t) v)
    (velocity : w = Complex.orientation.rightAngleRotation (f t - h) + slide • v) :
    deriv (fun x => Complex.arg (f x / f t)) t ≤ 2 / m := by
  have sq := derivative.hasFDerivAt.norm_sq
  have eq : (fun x => ‖f x‖ ^ 2) =ᶠ[𝓝 t] fun _ => ‖f t‖ ^ 2 :=
    constant_radius.mono (fun _ hx => congrArg (fun r : ℝ => r ^ 2) hx)
  have zero := sq.unique ((hasFDerivAt_const (‖f t‖ ^ 2) t).congr_of_eventuallyEq eq)
  have eval := DFunLike.congr_fun zero (1 : ℝ)
  have tangent : inner ℝ (f t) w = 0 := by
    simp only [two_nsmul, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_apply] at eval
    linarith only [eval]
  rw [(hasDerivAt_circleContact_angle derivative nonzero constant_radius).deriv]
  exact hingeCircle_angularSpeed_le Complex.orientation m_pos nonzero v_ne margin hinge
    velocity tangent

end Unfoldings
