module

public import Unfoldings.Geometry.GnomonicStraightHinge
public import Unfoldings.Roof.SharpStraightLink

/-! The signed turn of a straight horizontal closing link at its actual crease. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

local notation "east" => (WithLp.toLp 2 ![(1 : ℝ), 0] : Plane)

theorem sectionDirection_east (f : Face) :
    K.sectionDirection f east = WithLp.toLp 2 ![1, 0, -(K.normalSlope f) 0] := by
  have scalar : inner ℝ (K.normalSlope f) east = K.normalSlope f 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  rw [sectionDirection, scalar]
  rfl

/-- For a crease ray on the upper side of the link, the difference of the
two ordinary corner angles is the signed hinge change along the normal segment.
Both normals lie on exactly the displayed line in slope space. -/
theorem signed_horizontal_sectionHinge (l r : Face) (join : Plane)
    (above : 0 < join 1)
    (tie : inner ℝ (K.normalSlope l - K.normalSlope r) join = 0) :
    let p := K.normalSlope r 0
    let q := K.normalSlope l 0
    let m := -(join 0) / join 1
    let b := K.normalSlope l 1 - m * q
    K.normalSlope r 1 = m * p + b ∧ K.normalSlope l 1 = m * q + b ∧
      angle (K.sectionDirection l join) (K.sectionDirection r east) -
        angle (K.sectionDirection l join) (K.sectionDirection l east) =
          hingeAngleChange m b p q := by
  let p := K.normalSlope r 0
  let q := K.normalSlope l 0
  let m := -(join 0) / join 1
  let b := K.normalSlope l 1 - m * q
  have eastward : join 1 * (-m) = join 0 := by
    dsimp only [m]
    rw [neg_div, neg_neg, mul_div, mul_comm (join 1), mul_div_cancel_right₀ _ above.ne']
  have equation_left : K.normalSlope l 1 = m * q + b := by dsimp only [b]; ring
  have equation_right : K.normalSlope r 1 = m * p + b := by
    have horizontal := PiLp.inner_apply (𝕜 := ℝ) (K.normalSlope l - K.normalSlope r) join
    rw [Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at horizontal
    rw [tie] at horizontal
    change 0 = (q - p) * join 0 + ((K.normalSlope l) 1 - (K.normalSlope r) 1) * join 1 at horizontal
    apply (mul_left_cancel₀ above.ne')
    rw [← eastward] at horizontal
    rw [equation_left] at horizontal
    nlinarith only [horizontal]
  have lift : K.sectionDirection l join = (join 1) •
      (WithLp.toLp 2 ![-m, 1, -b] : Space) := by
    ext i
    fin_cases i
    · change join 0 = join 1 * (-m)
      exact eastward.symm
    · change join 1 = join 1 * 1
      rw [mul_one]
    · change -inner ℝ (K.normalSlope l) join = join 1 * (-b)
      rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply]
      change -(q * join 0 + K.normalSlope l 1 * join 1) = _
      rw [← eastward, equation_left]
      ring
  refine ⟨equation_right, equation_left, ?_⟩
  rw [lift, angle_smul_left_of_pos _ _ above, angle_smul_left_of_pos _ _ above,
    sectionDirection_east, sectionDirection_east, ← straightHingeAngle_eq_angle,
    ← straightHingeAngle_eq_angle]
  exact straightHinge_sub_eq_hingeAngleChange m b p q

end Unfoldings.ConvexRoof
