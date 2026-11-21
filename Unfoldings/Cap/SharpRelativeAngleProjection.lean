module

public import Unfoldings.Cap.RelativeFaceAngleError
public import Unfoldings.Geometry.LinearAngleDistortion

/-! The relative angle estimate for a whole projected fan at the sharp constant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexCap C)

/-- A face projection, and its inverse, distort angles by at most the secant
of the tilt. This gives a relative estimate that can be summed over a fan. -/
theorem abs_face_projection_angle_error_le_sec {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (f : Face) {x y : Plane} (xn : x ≠ 0) (yn : y ≠ 0) :
    let A := (K.projectFaceEquiv f).linear
    |angle x y - angle (A x) (A y)| ≤ ((cos phi)⁻¹ - 1) * angle (A x) (A y) := by
  let A := (K.projectFaceEquiv f).linear
  let c := cos phi
  have cp : 0 < c := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], small⟩
  have cs : c ≤ 1 := cos_le_one _
  have lower (z : Plane) : c * ‖z‖ ≤ ‖A z‖ :=
    (mul_le_mul_of_nonneg_right (tilt f) (norm_nonneg _)).trans
      (K.face_projection_linear_bounds f z).1
  have upper (z : Plane) : ‖A z‖ ≤ 1 * ‖z‖ := by
    rw [one_mul]
    exact (K.face_projection_linear_bounds f z).2
  have lower_inv (z : Plane) : 1 * ‖z‖ ≤ ‖A.symm z‖ := by
    have h := upper (A.symm z)
    rw [A.apply_symm_apply, one_mul] at h
    simpa only [one_mul] using h
  have upper_inv (z : Plane) : ‖A.symm z‖ ≤ c⁻¹ * ‖z‖ := by
    have h := lower (A.symm z)
    rw [A.apply_symm_apply] at h
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ cp).mpr
    simpa only [mul_comm c ‖A.symm z‖] using h
  have xA : A x ≠ 0 := by simpa only [map_zero] using A.injective.ne xn
  have yA : A y ≠ 0 := by simpa only [map_zero] using A.injective.ne yn
  have forward := angle_plane_linear_le A.toLinearMap cp zero_le_one lower upper xn yn
  have back := angle_plane_linear_le A.symm.toLinearMap zero_lt_one (inv_nonneg.mpr cp.le)
    lower_inv upper_inv xA yA
  change angle (A x) (A y) ≤ 1 / c * angle x y at forward
  change angle (A.symm (A x)) (A.symm (A y)) ≤ c⁻¹ / 1 * angle (A x) (A y) at back
  rw [A.symm_apply_apply, A.symm_apply_apply, div_one] at back
  have forward' : c * angle (A x) (A y) ≤ angle x y := by
    rw [div_mul_eq_mul_div, one_mul] at forward
    simpa only [mul_comm (angle (A x) (A y)) c] using (le_div_iff₀ cp).mp forward
  have reciprocal : 1 - c ≤ c⁻¹ - 1 := by
    have h := (le_div_iff₀ cp).mpr (mul_le_of_le_one_right (sub_nonneg.mpr cs) cs)
    simpa only [sub_div, div_self cp.ne', one_div] using h
  have compare := mul_le_mul_of_nonneg_right reciprocal (angle_nonneg (A x) (A y))
  change |angle x y - angle (A x) (A y)| ≤ (c⁻¹ - 1) * angle (A x) (A y)
  apply abs_le.mpr
  constructor <;> linarith only [forward', back, compare]

/-- The projected angle of a subdivided fan can be multiplied by the same
relative error constant regardless of the number of corners in the fan. -/
theorem relativeCornerAngleError_sec_tilt {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi) :
    K.RelativeCornerAngleError ((cos phi)⁻¹ - 1) := by
  intro f i
  let T := C.triangle f
  have first_ne : T.vertex (Triangle.next i) - T.vertex i ≠ 0 :=
    sub_ne_zero.mpr (T.edge_endpoints_ne i).symm
  have last_ne : T.vertex (Triangle.next (Triangle.next i)) - T.vertex i ≠ 0 := by
    apply sub_ne_zero.mpr
    apply T.vertex_injective.ne
    fin_cases i <;> decide
  have bound := K.abs_face_projection_angle_error_le_sec nonnegative small tilt f first_ne last_ne
  dsimp only at bound
  have chord (j : Fin 3) : (K.projectFaceEquiv f).linear (T.vertex j - T.vertex i) =
      (K.projectedTriangle f).vertex j - (K.projectedTriangle f).vertex i :=
    (K.projectFaceEquiv f).toAffineMap.linear_apply_vsub (T.vertex j) (T.vertex i)
  rw [chord, chord] at bound
  exact bound

end Unfoldings.ConvexCap
