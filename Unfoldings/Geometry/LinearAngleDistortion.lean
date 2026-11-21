module

public import Unfoldings.Geometry.SphericalPathAngle
public import Unfoldings.Geometry.PolarAngleBound
public import Unfoldings.Geometry.Normalize
public import Mathlib.Analysis.Complex.Angle

/-! Angular distortion of a planar linear map from its norm bounds. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry NormedSpace

private theorem angle_normalize_normalize {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E} (un : u ≠ 0) (vn : v ≠ 0) :
    angle (normalize u) (normalize v) = angle u v := by
  rw [NormedSpace.normalize, NormedSpace.normalize,
    angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr un)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr vn))]

private theorem angle_complex_linear_le_of_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : ℂ →ₗ[ℝ] E) {L U : ℝ}
    (positive : 0 < L) (speed : 0 ≤ U)
    (lower : ∀ z, L * ‖z‖ ≤ ‖A z‖) (upper : ∀ z, ‖A z‖ ≤ U * ‖z‖)
    {x y : ℂ} (xu : ‖x‖ = 1) (yu : ‖y‖ = 1) :
    angle (A x) (A y) ≤ U / L * angle x y := by
  have xn : x ≠ 0 := norm_ne_zero_iff.mp (by rw [xu]; norm_num)
  have yn : y ≠ 0 := norm_ne_zero_iff.mp (by rw [yu]; norm_num)
  let a := (y / x).arg
  have abs_a : |a| = angle x y := by
    rw [angle_comm x y, Complex.angle_eq_abs_arg yn xn]
  have unit_div : ‖y / x‖ = 1 := by rw [norm_div, xu, yu, div_one]
  have phase : polarRay a = y / x := by
    have rep := Complex.norm_mul_exp_arg_mul_I (y / x)
    rw [unit_div, Complex.ofReal_one, one_mul] at rep
    exact rep
  let circle (t : ℝ) := x * polarRay t
  have at_zero : circle 0 = x := by simp [circle, polarRay_zero]
  have at_end : circle a = y := by
    dsimp [circle]
    rw [phase, mul_div_cancel₀ _ xn]
  have circle_unit (t : ℝ) : ‖circle t‖ = 1 := by
    simp only [circle, norm_mul, xu, norm_polarRay, mul_one]
  let f (t : ℝ) := normalize (A (circle t))
  have norm_ge (t : ℝ) : L ≤ ‖A (circle t)‖ := by simpa [circle_unit] using lower (circle t)
  have nonzero (t : ℝ) : A (circle t) ≠ 0 :=
    norm_pos_iff.mp (positive.trans_le (norm_ge t))
  have unit (t : ℝ) : ‖f t‖ = 1 := norm_normalize (nonzero t)
  have chords (u v : ℝ) : ‖f v - f u‖ ≤ U / L * |v - u| := by
    have scale (t : ℝ) : 1 ≤ ‖L⁻¹ • A (circle t)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), ← div_eq_inv_mul,
        le_div_iff₀ positive, one_mul]
      exact norm_ge t
    have h := dist_normalize_le (scale v) (scale u)
    simp only [normalize_smul_of_pos (inv_pos.mpr positive), dist_eq_norm, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), ← map_sub] at h
    have short : ‖circle v - circle u‖ ≤ |v - u| := by
      apply (norm_sub_le_angle_of_unit (circle_unit v) (circle_unit u)).trans
      unfold circle
      have vne : x * polarRay v ≠ 0 := mul_ne_zero xn (polarRay_ne_zero v)
      have une : x * polarRay u ≠ 0 := mul_ne_zero xn (polarRay_ne_zero u)
      rw [Complex.angle_eq_abs_arg vne une, mul_div_mul_left _ _ xn,
        ← Complex.angle_eq_abs_arg (polarRay_ne_zero v) (polarRay_ne_zero u)]
      exact angle_polarRay_le_abs_sub v u |>.trans_eq (abs_sub_comm _ _)
    apply h.trans
    calc
      L⁻¹ * ‖A (circle v - circle u)‖ ≤ L⁻¹ * (U * ‖circle v - circle u‖) :=
        mul_le_mul_of_nonneg_left (upper _) (inv_nonneg.mpr positive.le)
      _ ≤ L⁻¹ * (U * |v - u|) := by gcongr
      _ = _ := by rw [div_eq_inv_mul, mul_assoc]
  have bound := angle_le_chord_speed f unit (div_nonneg speed positive.le) chords 0 a
  change angle (normalize (A (circle 0))) (normalize (A (circle a))) ≤ _ at bound
  rw [angle_normalize_normalize (nonzero 0) (nonzero a), at_zero, at_end, sub_zero, abs_a] at bound
  exact bound

/-- A planar linear map increases angles by at most its norm condition bound. -/
theorem angle_complex_linear_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : ℂ →ₗ[ℝ] E) {L U : ℝ}
    (positive : 0 < L) (speed : 0 ≤ U)
    (lower : ∀ z, L * ‖z‖ ≤ ‖A z‖) (upper : ∀ z, ‖A z‖ ≤ U * ‖z‖)
    {x y : ℂ} (xn : x ≠ 0) (yn : y ≠ 0) :
    angle (A x) (A y) ≤ U / L * angle x y := by
  have bound := angle_complex_linear_le_of_unit A positive speed lower upper
    (norm_normalize xn) (norm_normalize yn)
  rw [angle_normalize_normalize xn yn] at bound
  simp only [NormedSpace.normalize, map_smul,
    angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr xn)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr yn))] at bound
  exact bound

/-- The same condition bound in Euclidean coordinates. -/
theorem angle_plane_linear_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : Plane →ₗ[ℝ] E) {L U : ℝ}
    (positive : 0 < L) (speed : 0 ≤ U)
    (lower : ∀ z, L * ‖z‖ ≤ ‖A z‖) (upper : ∀ z, ‖A z‖ ≤ U * ‖z‖)
    {x y : Plane} (xn : x ≠ 0) (yn : y ≠ 0) :
    angle (A x) (A y) ≤ U / L * angle x y := by
  let P := Complex.orthonormalBasisOneI.repr
  let B := A.comp P.toLinearEquiv.toLinearMap
  have lower_B (z : ℂ) : L * ‖z‖ ≤ ‖B z‖ := by
    change L * ‖z‖ ≤ ‖A (P z)‖
    rw [← P.norm_map z]
    exact lower _
  have upper_B (z : ℂ) : ‖B z‖ ≤ U * ‖z‖ := by
    change ‖A (P z)‖ ≤ U * ‖z‖
    rw [← P.norm_map z]
    exact upper _
  have eq (z : Plane) : B (P.symm z) = A z := by
    change A (P (P.symm z)) = A z
    rw [P.apply_symm_apply]
  have h := angle_complex_linear_le B positive speed lower_B upper_B
    (by simpa only [map_zero] using P.symm.injective.ne xn)
    (by simpa only [map_zero] using P.symm.injective.ne yn)
  have theta : angle (P.symm x) (P.symm y) = angle x y :=
    P.symm.toLinearIsometry.angle_map x y
  rw [eq, eq, theta] at h
  exact h

end Unfoldings
