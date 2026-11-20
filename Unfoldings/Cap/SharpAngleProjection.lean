module

public import Unfoldings.Cap.Projection
public import Unfoldings.Geometry.AngleConeBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Sharp angle distortion from tilted-face projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

/-- Angle between a nonzero vector and its contraction by a symmetric map with
eigenvalues (1,c), expressed through their exact inner-product identity. -/
theorem angle_le_arcsin_of_contraction_identity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x y : E} (x_ne : x ≠ 0) (y_ne : y ≠ 0)
    {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1)
    (identity : ‖y‖ ^ 2 + c * ‖x‖ ^ 2 = (1 + c) * inner ℝ x y) :
    angle x y ≤ arcsin ((1 - c) / (1 + c)) := by
  let α := angle x y
  let N := ‖x‖ * ‖y‖
  have N_pos : 0 < N := mul_pos (norm_pos_iff.mpr x_ne) (norm_pos_iff.mpr y_ne)
  have factor : 0 < 1 + c := by positivity
  have inner_nonneg : 0 ≤ inner ℝ x y := by
    apply nonneg_of_mul_nonneg_right _ factor
    rw [← identity]
    positivity
  have acute : α ≤ π / 2 := le_of_not_gt (fun h =>
    (not_lt_of_ge inner_nonneg) (inner_neg_iff_pi_div_two_lt_angle.mpr h))
  have sin_nonneg : 0 ≤ sin α := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _) (angle_le_pi _ _)
  have cos_eq : cos α * N = inner ℝ x y := cos_angle_mul_norm_mul_norm _ _
  have square : ((1 + c) * (sin α * N)) ^ 2 ≤ ((1 - c) * N) ^ 2 := calc
    _ = ((1 + c) * N) ^ 2 - ((1 + c) * inner ℝ x y) ^ 2 := by
      rw [← cos_eq]
      linear_combination ((1 + c) * N) ^ 2 * sin_sq_add_cos_sq α
    _ ≤ _ := by
      rw [← identity]
      dsimp only [N]
      nlinarith [sq_nonneg (‖y‖ ^ 2 - c * ‖x‖ ^ 2)]
  have scalar := (sq_le_sq₀ (by positivity) (mul_nonneg (sub_nonneg.mpr c_le) N_pos.le)).mp square
  have sin_le : sin α ≤ (1 - c) / (1 + c) := by
    apply (le_div_iff₀ factor).mpr
    apply le_of_mul_le_mul_right (a := N) _ N_pos
    simpa only [mul_assoc, mul_left_comm, mul_comm] using scalar
  change α ≤ _
  rw [← arcsin_sin (by linarith [angle_nonneg x y, pi_pos]) acute]
  exact arcsin_le_arcsin sin_le

namespace Cap

/-- The horizontal coordinates of the isometric alignment of a tangent plane
with the horizontal plane. Unlike orthogonal projection, it preserves angles. -/
def alignedHorizontal (normal x : Space) : Plane :=
  horizontal x - (x 2 / (1 + normal 2)) • horizontal normal

theorem alignedHorizontal_inner {n x y : Space} (unit : ‖n‖ = 1) (positive : 0 < n 2)
    (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    inner ℝ (alignedHorizontal n x) (alignedHorizontal n y) = inner ℝ x y := by
  have normal_sq : ‖horizontal n‖ ^ 2 = 1 - (n 2) ^ 2 := by
    have h := horizontal_norm_sq n
    rw [unit] at h
    linarith
  have tangent_x : inner ℝ (horizontal n) (horizontal x) = -(n 2 * x 2) := by
    linarith [horizontal_inner n x]
  have tangent_y : inner ℝ (horizontal n) (horizontal y) = -(n 2 * y 2) := by
    linarith [horizontal_inner n y]
  have xy : inner ℝ (horizontal x) (horizontal y) = inner ℝ x y - x 2 * y 2 := by
    linarith [horizontal_inner x y]
  have symmetry : inner ℝ (horizontal x) (horizontal n) = inner ℝ (horizontal n) (horizontal x) :=
    real_inner_comm _ _
  unfold alignedHorizontal
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, normal_sq, symmetry, xy, tangent_x, tangent_y]
  field_simp [show 1 + n 2 ≠ 0 by positivity]
  ring

theorem alignedHorizontal_norm {n x : Space} (unit : ‖n‖ = 1) (positive : 0 < n 2)
    (tangent : inner ℝ n x = 0) : ‖alignedHorizontal n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using alignedHorizontal_inner unit positive tangent tangent

theorem alignedHorizontal_projection_identity {n x : Space} (unit : ‖n‖ = 1)
    (positive : 0 < n 2) (tangent : inner ℝ n x = 0) :
    ‖horizontal x‖ ^ 2 + (n 2) * ‖alignedHorizontal n x‖ ^ 2 =
      (1 + n 2) * inner ℝ (alignedHorizontal n x) (horizontal x) := by
  have dot : inner ℝ (horizontal n) (horizontal x) = -(n 2 * x 2) := by
    linarith [horizontal_inner n x]
  rw [alignedHorizontal_norm unit positive tangent]
  simp only [alignedHorizontal, inner_sub_left, real_inner_smul_left, dot,
    real_inner_self_eq_norm_sq]
  field_simp [show 1 + n 2 ≠ 0 by positivity]
  nlinarith [horizontal_norm_sq x, congrArg (fun t : ℝ => n 2 * t) (horizontal_norm_sq x)]

/-- The angular distortion of horizontal projection on a plane with upward
unit normal is at most twice the sharp one-direction error. -/
theorem tangent_projection_angle_error {n x y : Space} (unit : ‖n‖ = 1) {c : ℝ}
    (c_pos : 0 < c) (tilt : c ≤ n 2) (x_ne : x ≠ 0) (y_ne : y ≠ 0)
    (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    |angle (horizontal x) (horizontal y) - angle x y| ≤ 2 * arcsin ((1 - c) / (1 + c)) := by
  have up := c_pos.trans_le tilt
  have n_le : n 2 ≤ 1 := by
    have h := horizontal_norm_sq n
    rw [unit] at h
    nlinarith [sq_nonneg ‖horizontal n‖]
  let Δ := arcsin ((1 - c) / (1 + c))
  have ratio : (1 - n 2) / (1 + n 2) ≤ (1 - c) / (1 + c) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have direction {z : Space} (nz : z ≠ 0) (tz : inner ℝ n z = 0) :
      angle (alignedHorizontal n z) (horizontal z) ≤ Δ := by
    have ne_align : alignedHorizontal n z ≠ 0 := by
      intro zero
      have h := alignedHorizontal_norm unit up tz
      rw [zero, norm_zero] at h
      exact nz (norm_eq_zero.mp h.symm)
    exact (angle_le_arcsin_of_contraction_identity ne_align
      (tangent_horizontal_ne_zero n z unit up tz nz) up n_le
      (alignedHorizontal_projection_identity unit up tz)).trans (arcsin_le_arcsin ratio)
  have angles : angle (alignedHorizontal n x) (alignedHorizontal n y) = angle x y := by
    rw [angle, angle, alignedHorizontal_inner unit up tx ty, alignedHorizontal_norm unit up tx,
      alignedHorizontal_norm unit up ty]
  have hx := direction x_ne tx
  have hy := direction y_ne ty
  have projected_first := angle_le_angle_add_angle (horizontal x) (alignedHorizontal n x) (horizontal y)
  have projected_last := angle_le_angle_add_angle (alignedHorizontal n x) (alignedHorizontal n y)
    (horizontal y)
  have aligned_first := angle_le_angle_add_angle (alignedHorizontal n x) (horizontal x)
    (alignedHorizontal n y)
  have aligned_last := angle_le_angle_add_angle (horizontal x) (horizontal y) (alignedHorizontal n y)
  rw [angle_comm (horizontal x) (alignedHorizontal n x)] at projected_first
  rw [angle_comm (horizontal y) (alignedHorizontal n y)] at aligned_last
  rw [angles] at projected_last aligned_first
  apply abs_le.mpr
  constructor <;> linarith

end Cap
end Unfoldings
