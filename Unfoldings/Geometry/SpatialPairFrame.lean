module

public import Unfoldings.Geometry.TwoVectorFrame
public import Unfoldings.Geometry.Azimuth
public import Unfoldings.Cone.Sector

/-! Orthogonal normal forms for arbitrary pairs of genuine spatial directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Isometrically include the standard complex plane at height zero. -/
def complexLift : ℂ →ₗᵢ[ℝ] Space :=
  Cap.horizontalLiftIsometry.comp Complex.orthonormalBasisOneI.repr.toLinearIsometry

theorem complexLift_apply (w : ℂ) : complexLift w = WithLp.toLp 2 ![w.re, w.im, 0] := by
  ext i
  fin_cases i
  · change (Complex.orthonormalBasisOneI.repr w).ofLp 0 = w.re
    rw [Complex.orthonormalBasisOneI_repr_apply]
    rfl
  · change (Complex.orthonormalBasisOneI.repr w).ofLp 1 = w.im
    rw [Complex.orthonormalBasisOneI_repr_apply]
    rfl
  · rfl

theorem complexHorizontal_apply (z : Space) : complexHorizontal z = z 0 + z 1 * Complex.I := by
  change Complex.orthonormalBasisOneI.repr.symm (Cap.horizontal z) = _
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  rfl

/-- Spatial scalar products against horizontal vectors use their actual complex coordinates. -/
theorem inner_complexLift (z : Space) (w : ℂ) :
    inner ℝ z (complexLift w) =
      (complexHorizontal z).re * w.re + (complexHorizontal z).im * w.im := by
  rw [complexLift_apply, complexHorizontal_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- The second vector can lie on either real ray; its imaginary part is nonnegative. -/
theorem exists_pair_frame_upper (u v : Space) (nonzero : u ≠ 0) :
    ∃ (L : Space ≃ₗᵢ[ℝ] Space) (w : ℂ), 0 ≤ w.im ∧
      L u = complexLift (‖u‖ : ℂ) ∧ L v = complexLift w := by
  obtain ⟨B, c, d, nonnegative, first, second⟩ :=
    exists_basis_two_vector_decomposition u v nonzero
  let L : Space ≃ₗᵢ[ℝ] Space := B.repr
  let w : ℂ := c + d * Complex.I
  have basis0 : L (B 0) = EuclideanSpace.single 0 (1 : ℝ) := B.repr_self 0
  have basis1 : L (B 1) = EuclideanSpace.single 1 (1 : ℝ) := B.repr_self 1
  refine ⟨L, w, ?_, ?_, ?_⟩
  · simpa only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using nonnegative
  · calc
      L u = L (‖u‖ • B 0) := congrArg L first
      _ = complexLift (‖u‖ : ℂ) := by
        rw [map_smul, basis0, complexLift_apply]
        ext i
        fin_cases i <;> simp
  · calc
      L v = L (c • B 0 + d • B 1) := congrArg L second
      _ = complexLift w := by
        rw [map_add, map_smul, map_smul, basis0, basis1, complexLift_apply]
        ext i
        fin_cases i <;> simp [w]

/-- A pair can be placed at real headings zero and its actual unoriented angle. -/
theorem exists_pair_frame (u v : Space) (first_nonzero : u ≠ 0) (last_nonzero : v ≠ 0) :
    ∃ L : Space ≃ₗᵢ[ℝ] Space,
      L u = ‖u‖ • complexLift 1 ∧
      L v = ‖v‖ • complexLift (polarRay (InnerProductGeometry.angle u v)) := by
  obtain ⟨L, w, upper, first, last⟩ := exists_pair_frame_upper u v first_nonzero
  have wne : w ≠ 0 := by
    intro zero
    rw [zero, map_zero] at last
    exact last_nonzero (L.injective (last.trans (map_zero L).symm))
  have normed : ‖w‖ = ‖v‖ := by
    have normed := congrArg norm last
    simpa only [L.norm_map, complexLift.norm_map] using normed.symm
  have first_pos : 0 < ‖u‖ := norm_pos_iff.mpr first_nonzero
  have angle : InnerProductGeometry.angle (‖u‖ : ℂ) w = w.arg := by
    have real_vector : (‖u‖ : ℂ) = ‖u‖ • (1 : ℂ) := by simp [Complex.real_smul]
    rw [real_vector, InnerProductGeometry.angle_smul_left_of_pos _ _ first_pos,
      Complex.angle_one_left wne, abs_of_nonneg (Complex.arg_nonneg_iff.mpr upper)]
  have argument : w.arg = InnerProductGeometry.angle u v := by
    have mapped := L.toLinearIsometry.angle_map u v
    change InnerProductGeometry.angle (L u) (L v) = InnerProductGeometry.angle u v at mapped
    rw [first, last, complexLift.angle_map, angle] at mapped
    exact mapped
  have polar := (Complex.norm_mul_exp_arg_mul_I w).symm
  change w = (‖w‖ : ℂ) * polarRay w.arg at polar
  rw [normed, argument] at polar
  refine ⟨L, ?_, ?_⟩
  · rw [first, ← map_smul]
    congr 1
    simp [Complex.real_smul]
  · rw [last, polar, ← Complex.real_smul, map_smul]

end Unfoldings
