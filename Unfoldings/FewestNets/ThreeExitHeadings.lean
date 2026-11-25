module

public import Unfoldings.Geometry.PlanarConjugation
public import Unfoldings.Geometry.PolarHeadingInterval
public import Unfoldings.FewestNets.ThreeExitPlane

/-! Heading estimates in the east-facing and west-facing charts of a selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

/-- The optional reflection sends the chosen horizontal direction to positive
real and keeps north positive imaginary. -/
def exitHeadingChart (west : Bool) : Plane ≃ₗᵢ[ℝ] ℂ :=
  if west then (planeConjugation.trans Complex.orthonormalBasisOneI.repr.symm).trans
    (LinearIsometryEquiv.neg ℝ)
  else Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem exitHeadingChart_re (west : Bool) (d : Plane) :
    (exitHeadingChart west d).re = if west then -d 0 else d 0 := by
  cases west <;> simp [exitHeadingChart, planeConjugation_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

@[simp] theorem exitHeadingChart_im (west : Bool) (d : Plane) :
    (exitHeadingChart west d).im = d 1 := by
  cases west <;> simp [exitHeadingChart, planeConjugation_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

private theorem re_pos_of_arg {z : ℂ} (nonzero : z ≠ 0)
    (h : z.arg ∈ Set.Ioo (-(π / 2)) (π / 2)) : 0 < z.re := by
  rw [← Complex.norm_mul_cos_arg]
  exact mul_pos (norm_pos_iff.mpr nonzero) (cos_pos_of_mem_Ioo h)

private theorem im_pos_of_arg {z : ℂ} (nonzero : z ≠ 0)
    (h : z.arg ∈ Set.Ioo 0 π) : 0 < z.im := by
  rw [← Complex.norm_mul_sin_arg]
  exact mul_pos (norm_pos_iff.mpr nonzero) (sin_pos_of_pos_of_lt_pi h.1 h.2)

/-- A near-diagonal stem advances north and in its assigned horizontal direction. -/
theorem threeExit_stem_advances (west : Bool) {d : Plane} (nonzero : d ≠ 0)
    {δ : ℝ} (δ_pos : 0 < δ)
    (heading : (exitHeadingChart west d).arg ∈ Set.Icc δ (π / 2 - δ)) :
    0 < (if west then -d 0 else d 0) ∧ 0 < d 1 := by
  have genuine : exitHeadingChart west d ≠ 0 := by simpa using nonzero
  constructor
  · rw [← exitHeadingChart_re]
    exact re_pos_of_arg genuine
      ⟨by linarith only [pi_pos, δ_pos, heading.1], by linarith only [δ_pos, heading.2]⟩
  · rw [← exitHeadingChart_im west]
    exact im_pos_of_arg genuine
      ⟨δ_pos.trans_le heading.1, by linarith only [pi_pos, δ_pos, heading.2]⟩

/-- A near-horizontal exit advances in its own horizontal coordinate. -/
theorem threeExit_horizontal_advances (west : Bool) {d : Plane} (nonzero : d ≠ 0)
    {ε : ℝ} (ε_upper : ε < π / 2)
    (heading : (exitHeadingChart west d).arg ∈ Set.Icc (-ε) ε) :
    0 < (if west then -d 0 else d 0) := by
  have genuine : exitHeadingChart west d ≠ 0 := by simpa using nonzero
  rw [← exitHeadingChart_re]
  exact re_pos_of_arg genuine ⟨(neg_lt_neg ε_upper).trans_le heading.1,
    heading.2.trans_lt ε_upper⟩

/-- A stem approaching a forced horizontal exit from the other side lies
strictly below its supporting line. Each vector is expressed in its own
horizontal chart before comparing their slopes. -/
theorem threeExit_stem_below_horizontal_exit {stem ray : ℂ}
    (stem_ne : stem ≠ 0) (ray_ne : ray ≠ 0) {δ ε : ℝ}
    (ε_nonneg : 0 ≤ ε) (ε_lt : ε < δ)
    (stem_arg : stem.arg ∈ Set.Icc δ (π / 2 - δ))
    (ray_arg : ray.arg ∈ Set.Icc (-ε) ε) :
    0 < ray.re ∧ -stem.im < (ray.im / ray.re) * stem.re := by
  have δ_pos : 0 < δ := ε_nonneg.trans_lt ε_lt
  have stem_right : stem.arg < π / 2 := by linarith only [stem_arg.2, δ_pos]
  have ray_left : -(π / 2) < ray.arg := by
    linarith only [stem_arg.1, stem_arg.2, ray_arg.1, ε_lt, pi_pos]
  have ray_right : ray.arg < π / 2 := by
    linarith only [stem_arg.1, stem_arg.2, ray_arg.2, ε_lt, δ_pos]
  have reflected_left : -(π / 2) < -ray.arg := by linarith only [ray_right]
  have ordered : -ray.arg < stem.arg := by linarith only [ray_arg.1, ε_lt, stem_arg.1]
  have stem_re := re_pos_of_arg stem_ne ⟨reflected_left.trans ordered, stem_right⟩
  have ray_re := re_pos_of_arg ray_ne ⟨ray_left, ray_right⟩
  have slopes := tan_lt_tan_of_lt_of_lt_pi_div_two reflected_left stem_right ordered
  rw [tan_neg, Complex.tan_arg, Complex.tan_arg] at slopes
  have comparison := (lt_div_iff₀ stem_re).mp slopes
  exact ⟨ray_re, by simpa only [neg_mul, neg_neg] using neg_lt_neg comparison⟩

/-- The direction lemma gives stems in the same literal northeast interval in
each of the two charts. -/
theorem threeExit_heading_of_near_diagonal (west : Bool) {d : Plane}
    (nonzero : d ≠ 0) {δ : ℝ} (δ_pos : 0 < δ)
    (heading : angle ((exitHeadingChart west).symm (polarRay (π / 4))) d ≤ π / 4 - δ) :
    (exitHeadingChart west d).arg ∈ Set.Icc δ (π / 2 - δ) := by
  have genuine : exitHeadingChart west d ≠ 0 := by simpa using nonzero
  have mapped := (exitHeadingChart west).toLinearIsometry.angle_map
    ((exitHeadingChart west).symm (polarRay (π / 4))) d
  rw [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply] at mapped
  obtain ⟨lo, hi⟩ := arg_mem_Icc_of_angle_polarRay_le genuine
    (by linarith only [pi_pos, δ_pos] : -π < π / 4 - (π / 4 - δ))
    (by linarith only [pi_pos, δ_pos] : π / 4 + (π / 4 - δ) ≤ π)
    (mapped.trans_le heading)
  exact ⟨by linarith only [lo], by linarith only [hi]⟩

end Unfoldings.FewestNets
