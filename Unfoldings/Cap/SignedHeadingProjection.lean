module

public import Unfoldings.Cap.SharpAngleProjection
public import Unfoldings.Geometry.SignedPlanarAngle

/-! The signed projection error of a planar corner is the difference of
its two individual direction errors in the pole-aligned tangent frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real InnerProductGeometry

/-- The change in one direction's heading under pole alignment, relative to
its horizontal projection. -/
def projectionHeadingError (n x : Space) : ℝ :=
  signedPlanarAngle (horizontal x) (alignedHorizontal n x)

theorem abs_projectionHeadingError_le {n x : Space} (unit : ‖n‖ = 1) {c : ℝ}
    (c_pos : 0 < c) (tilt : c ≤ n 2) (nx : x ≠ 0) (tx : inner ℝ n x = 0) :
    |projectionHeadingError n x| ≤ arcsin ((1 - c) / (1 + c)) := by
  have up := c_pos.trans_le tilt
  have horizontal_ne := tangent_horizontal_ne_zero n x unit up tx nx
  have aligned_ne : alignedHorizontal n x ≠ 0 :=
    norm_pos_iff.mp (by rw [alignedHorizontal_norm unit up tx]; exact norm_pos_iff.mpr nx)
  rw [projectionHeadingError, abs_signedPlanarAngle _ _ horizontal_ne aligned_ne, angle_comm]
  exact alignedHorizontal_projection_angle_le unit c_pos tilt nx tx

private theorem alignedHorizontal_as_symmetric (n x : Space) (up : 0 < n 2)
    (tx : inner ℝ n x = 0) :
    alignedHorizontal n x =
      horizontal x + (inner ℝ (horizontal n) (horizontal x) / (n 2 * (1 + n 2))) • horizontal n := by
  have parallel : x 2 = -(inner ℝ (horizontal n) (horizontal x)) / n 2 := by
    apply (eq_div_iff up.ne').mpr
    have h := horizontal_inner n x
    rw [tx] at h
    nlinarith only [h]
  rw [alignedHorizontal, parallel, neg_div, neg_div, ← div_div, neg_smul, sub_neg_eq_add]

private theorem alignedHorizontal_det_eq (n x y : Space) (unit : ‖n‖ = 1) (up : 0 < n 2)
    (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    let a := alignedHorizontal n x
    let b := alignedHorizontal n y
    let u := horizontal x
    let v := horizontal y
    a 0 * b 1 - a 1 * b 0 = (u 0 * v 1 - u 1 * v 0) / n 2 := by
  let h := horizontal n
  let u := horizontal x
  let v := horizontal y
  let c := n 2
  have ns : h 0 ^ 2 + h 1 ^ 2 + c ^ 2 = 1 := by
    have h := horizontal_norm_sq n
    rw [unit, one_pow, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at h
    exact h.symm
  dsimp only
  rw [alignedHorizontal_as_symmetric n x up tx, alignedHorizontal_as_symmetric n y up ty,
    PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Real.inner_apply]
  change (u 0 + ((h 0 * u 0 + h 1 * u 1) / (c * (1 + c))) * h 0) *
      (v 1 + ((h 0 * v 0 + h 1 * v 1) / (c * (1 + c))) * h 1) -
    (u 1 + ((h 0 * u 0 + h 1 * u 1) / (c * (1 + c))) * h 1) *
      (v 0 + ((h 0 * v 0 + h 1 * v 1) / (c * (1 + c))) * h 0) =
      (u 0 * v 1 - u 1 * v 0) / c
  have cp : 0 < c := up
  field_simp [cp.ne', show 1 + c ≠ 0 by positivity]
  linear_combination (u 0 * v 1 - u 1 * v 0) * (c ^ 2 + c) * ns

theorem signedPlanarAngle_aligned_nonneg_iff {n x y : Space} (unit : ‖n‖ = 1) (up : 0 < n 2)
    (nx : x ≠ 0) (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    0 ≤ signedPlanarAngle (alignedHorizontal n x) (alignedHorizontal n y) ↔
      0 ≤ signedPlanarAngle (horizontal x) (horizontal y) := by
  have normal_ne : alignedHorizontal n x ≠ 0 :=
    norm_pos_iff.mp (by rw [alignedHorizontal_norm unit up tx]; exact norm_pos_iff.mpr nx)
  have horizontal_ne := tangent_horizontal_ne_zero n x unit up tx nx
  rw [signedPlanarAngle_nonneg_iff _ _ normal_ne, signedPlanarAngle_nonneg_iff _ _ horizontal_ne,
    alignedHorizontal_det_eq n x y unit up tx ty]
  simpa only [zero_mul] using
    (le_div_iff₀ up : (0 : ℝ) ≤ _ / n 2 ↔ 0 * n 2 ≤ _)

theorem alignedHorizontal_angle {n x y : Space} (unit : ‖n‖ = 1) (up : 0 < n 2)
    (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    angle (alignedHorizontal n x) (alignedHorizontal n y) = angle x y := by
  rw [angle, angle, alignedHorizontal_inner unit up tx ty, alignedHorizontal_norm unit up tx,
    alignedHorizontal_norm unit up ty]

/-- The two directional errors give the exact signed corner error, with real
values throughout. Positive orientation and the sharp distortion bound
exclude an extra full turn when unwrapping the quotient arguments. -/
theorem signed_projection_angle_sub_eq {n x y : Space} (unit : ‖n‖ = 1) (up : 0 < n 2)
    (nx : x ≠ 0) (ny : y ≠ 0) (tx : inner ℝ n x = 0) (ty : inner ℝ n y = 0) :
    signedPlanarAngle (alignedHorizontal n x) (alignedHorizontal n y) -
      signedPlanarAngle (horizontal x) (horizontal y) =
        projectionHeadingError n y - projectionHeadingError n x := by
  let A := alignedHorizontal n x
  let B := alignedHorizontal n y
  let X := horizontal x
  let Y := horizontal y
  let S := signedPlanarAngle A B
  let P := signedPlanarAngle X Y
  let ε := arcsin ((1 - n 2) / (1 + n 2))
  have an : A ≠ 0 := norm_pos_iff.mp
    (by rw [show ‖A‖ = ‖x‖ from alignedHorizontal_norm unit up tx]; exact norm_pos_iff.mpr nx)
  have bn : B ≠ 0 := norm_pos_iff.mp
    (by rw [show ‖B‖ = ‖y‖ from alignedHorizontal_norm unit up ty]; exact norm_pos_iff.mpr ny)
  have xn : X ≠ 0 := tangent_horizontal_ne_zero n x unit up tx nx
  have yn : Y ≠ 0 := tangent_horizontal_ne_zero n y unit up ty ny
  have eq_x : |S| = angle x y := (abs_signedPlanarAngle A B an bn).trans
    (alignedHorizontal_angle unit up tx ty)
  have eq_y : |P| = angle X Y := abs_signedPlanarAngle X Y xn yn
  have compare : 0 ≤ S ↔ 0 ≤ P := signedPlanarAngle_aligned_nonneg_iff unit up nx tx ty
  have distortion := tangent_projection_angle_error unit up le_rfl nx ny tx ty
  change |angle X Y - angle x y| ≤ 2 * ε at distortion
  have hSP : |S - P| ≤ 2 * ε := by
    rw [← eq_x, ← eq_y] at distortion
    by_cases hp : 0 ≤ P
    · rw [abs_of_nonneg hp, abs_of_nonneg (compare.mpr hp)] at distortion
      simpa only [abs_sub_comm S P] using distortion
    · rw [abs_of_nonpos (le_of_not_ge hp), abs_of_nonpos (le_of_not_ge (mt compare.mp hp))] at distortion
      simpa only [neg_sub_neg] using distortion
  have err_x := abs_projectionHeadingError_le unit up le_rfl nx tx
  have err_y := abs_projectionHeadingError_le unit up le_rfl ny ty
  have ε_lt : 2 * ε < π := by
    have ratio : (1 - n 2) / (1 + n 2) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith only [up])
    have h : ε < π / 2 := arcsin_lt_pi_div_two.mpr ratio
    linarith only [h]
  let err := projectionHeadingError n y - projectionHeadingError n x
  have herr : |err| ≤ 2 * ε :=
    (abs_sub _ _).trans (by
      change |projectionHeadingError n x| ≤ ε at err_x
      change |projectionHeadingError n y| ≤ ε at err_y
      linarith only [err_x, err_y])
  have quotient : ((S - P : ℝ) : Real.Angle) = (err : Real.Angle) := by
    dsimp only [S, P, err, projectionHeadingError]
    change ((signedPlanarAngle A B - signedPlanarAngle X Y : ℝ) : Real.Angle) =
      ((signedPlanarAngle Y B - signedPlanarAngle X A : ℝ) : Real.Angle)
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, signedPlanarAngle_coe A B an bn,
      signedPlanarAngle_coe X Y xn yn, signedPlanarAngle_coe Y B yn bn,
      signedPlanarAngle_coe X A xn an]
    abel
  have uq (v : ℝ) (h : |v| ≤ 2 * ε) : ((v : Real.Angle).toReal) = v :=
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith only [(abs_le.mp h).1, ε_lt], by linarith only [(abs_le.mp h).2, ε_lt]⟩
  exact (uq (S - P) hSP).symm.trans ((congrArg Real.Angle.toReal quotient).trans (uq err herr))

@[simp] theorem projectionHeadingError_neg (n x : Space) :
    projectionHeadingError n (-x) = projectionHeadingError n x := by
  have a : alignedHorizontal n (-x) = -alignedHorizontal n x := by
    unfold alignedHorizontal
    rw [map_neg]
    change -horizontal x - ((-x 2) / (1 + n 2)) • horizontal n = _
    rw [neg_div, neg_smul]
    abel
  rw [projectionHeadingError, map_neg, a, signedPlanarAngle_neg_neg]
  rfl

end Unfoldings.Cap
