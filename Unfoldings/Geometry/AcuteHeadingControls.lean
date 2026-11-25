module

public import Unfoldings.Geometry.TwoLinkRegularApex
public import Unfoldings.Geometry.HeadingSpeedError
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A heading window narrower than a right angle supplies the two independent
coordinates for either regular two-link closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

variable (frame : Plane ≃ₗᵢ[ℝ] ℂ)

private theorem inner_polarRay_arg (θ : ℝ) (z : ℂ) :
    inner ℝ (polarRay θ) z = ‖z‖ * cos (z.arg - θ) := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im,
    ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z, cos_sub]
  ring

/-- The two diagonal coordinate directions in the bisector chart. -/
def headingControl (θ : ℝ) : Plane →L[ℝ] ℝ :=
  innerSL ℝ (frame.symm (polarRay θ))

theorem headingControl_apply (θ : ℝ) (p : Plane) :
    headingControl frame θ p = ‖p‖ * cos ((frame p).arg - θ) := by
  change inner ℝ (frame.symm (polarRay θ)) p = _
  rw [← frame.inner_map_map, frame.apply_symm_apply, inner_polarRay_arg,
    LinearIsometryEquiv.norm_map]

private theorem polarRay_inner (θ η : ℝ) : inner ℝ (polarRay θ) (polarRay η) = cos (η - θ) := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im,
    polarRay_re, polarRay_im, cos_sub]
  ring

/-- The two controls are independent, so shifting either supporting line is possible. -/
theorem headingControls_surjective (θ : ℝ) :
    Function.Surjective fun p =>
      (headingControl frame (θ + π / 4) p, headingControl frame (θ - π / 4) p) := by
  let e := frame.symm (polarRay (θ + π / 4))
  let f := frame.symm (polarRay (θ - π / 4))
  have eu : inner ℝ e e = 1 := by
    change inner ℝ (frame.symm _) (frame.symm _) = _
    rw [frame.symm.inner_map_map, polarRay_inner, sub_self, cos_zero]
  have fu : inner ℝ f f = 1 := by
    change inner ℝ (frame.symm _) (frame.symm _) = _
    rw [frame.symm.inner_map_map, polarRay_inner, sub_self, cos_zero]
  have orth : inner ℝ e f = 0 := by
    change inner ℝ (frame.symm _) (frame.symm _) = _
    rw [frame.symm.inner_map_map, polarRay_inner,
      show θ - π / 4 - (θ + π / 4) = -(π / 2) by ring, cos_neg, cos_pi_div_two]
  have reverse : inner ℝ f e = 0 := (real_inner_comm e f).trans orth
  rintro ⟨x, y⟩
  refine ⟨x • e + y • f, Prod.ext ?_ ?_⟩
  · change inner ℝ e (x • e + y • f) = x
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, eu, orth]
    ring
  · change inner ℝ f (x • e + y • f) = y
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, reverse, fu]
    ring

/-- The diagonal coordinates determine a point uniquely. -/
theorem headingControls_bijective (θ : ℝ) :
    Function.Bijective fun p =>
      (headingControl frame (θ + π / 4) p, headingControl frame (θ - π / 4) p) := by
  let L := (headingControl frame (θ + π / 4)).toLinearMap.prod
    (headingControl frame (θ - π / 4)).toLinearMap
  have dimension : Module.finrank ℝ Plane = Module.finrank ℝ (ℝ × ℝ) := by
    simp [Plane, Module.finrank_prod, finrank_euclideanSpace_fin]
  have onto : Function.Surjective L := headingControls_surjective frame θ
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimension).mpr onto, onto⟩

/-- Every nonzero direction in a strict acute interval advances both diagonal coordinates. -/
theorem headingControls_pos {p : Plane} (nonzero : p ≠ 0) {lo hi : ℝ}
    (acute : hi - lo < π / 2) (heading : (frame p).arg ∈ Set.Icc lo hi) :
    let middle := (lo + hi) / 2
    0 < headingControl frame (middle + π / 4) p ∧
      0 < headingControl frame (middle - π / 4) p := by
  have nonzero_norm := norm_pos_iff.mpr nonzero
  dsimp only
  constructor <;> rw [headingControl_apply] <;> apply mul_pos nonzero_norm <;>
    apply cos_pos_of_mem_Ioo <;>
    exact ⟨by linarith only [acute, heading.1, heading.2, pi_pos],
      by linarith only [acute, heading.1, heading.2, pi_pos]⟩

end Unfoldings
