module

public import Unfoldings.Geometry.HalfAngleDistortion
public import Unfoldings.Geometry.MinorArcArclength
public import Unfoldings.Cap.Gnomonic

/-! Great-circle tangents are orthogonal projections of the lifted chart directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Real InnerProductGeometry NormedSpace

private def tangentProjection (n : Space) : Space →ₗ[ℝ] Space :=
  LinearMap.id - (innerSL ℝ n).toLinearMap.smulRight n

private theorem tangentProjection_apply (n x : Space) :
    tangentProjection n x = x - inner ℝ n x • n := rfl

private theorem tangentProjection_self (n : Space) (unit : ‖n‖ = 1) :
    tangentProjection n n = 0 := by
  rw [tangentProjection_apply, real_inner_self_eq_norm_sq, unit, one_pow, one_smul, sub_self]

private theorem norm_tangentProjection_squared (n x : Space) (unit : ‖n‖ = 1) :
    ‖tangentProjection n x‖ ^ 2 = ‖x‖ ^ 2 - inner ℝ n x ^ 2 := by
  rw [tangentProjection_apply, norm_sub_pow_two_real, norm_smul, norm_eq_abs, unit,
    mul_one, sq_abs, real_inner_smul_right, real_inner_comm x n]
  ring

private theorem norm_tangentProjection_horizontal (n : Space) (unit : ‖n‖ = 1)
    (upward : 0 ≤ n 2) (x : Plane) :
    n 2 * ‖x‖ ≤ ‖tangentProjection n (horizontalLift x)‖ ∧
      ‖tangentProjection n (horizontalLift x)‖ ≤ ‖x‖ := by
  have sq := norm_tangentProjection_squared n (horizontalLift x) unit
  rw [horizontalLift_norm] at sq
  refine ⟨?_, (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (sq.trans_le (sub_le_self _ (sq_nonneg _)))⟩
  have horizontal_x : horizontal (horizontalLift x) = x := by ext i; fin_cases i <;> rfl
  have height_x : horizontalLift x 2 = 0 := rfl
  have perpendicular := horizontal_inner n (horizontalLift x)
  rw [horizontal_x, height_x, mul_zero, add_zero] at perpendicular
  have cauchy := real_inner_mul_inner_self_le (horizontal n) x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← perpendicular] at cauchy
  have normal_sq := horizontal_norm_sq n
  rw [unit, one_pow] at normal_sq
  have expand := congrArg (fun y : ℝ => y * ‖x‖ ^ 2) normal_sq
  apply (sq_le_sq₀ (mul_nonneg upward (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow]
  nlinarith only [expand, cauchy, sq]

private theorem gnomonic_angle_pos_lt_pi {p q : Plane} (different : p ≠ q) :
    0 < angle (gnomonicNormal p) (gnomonicNormal q) ∧
      angle (gnomonicNormal p) (gnomonicNormal q) < π := by
  let u := gnomonicNormal p
  let v := gnomonicNormal q
  refine ⟨lt_of_le_of_ne (angle_nonneg _ _) ?_, lt_of_le_of_ne (angle_le_pi _ _) ?_⟩
  · intro zero
    obtain ⟨_, t, positive, scaled⟩ := angle_eq_zero_iff.mp zero.symm
    have absolute : ‖gnomonicNormal q‖ = |t| * ‖gnomonicNormal p‖ := by
      rw [scaled, norm_smul, Real.norm_eq_abs]
    rw [gnomonicNormal_unit, gnomonicNormal_unit, abs_of_pos positive, mul_one] at absolute
    have same : gnomonicNormal q = gnomonicNormal p := by
      rw [scaled, ← absolute, one_smul]
    exact different (gnomonicNormal_injective same.symm)
  · intro straight
    obtain ⟨_, t, negative, scaled⟩ := angle_eq_pi_iff.mp straight
    have top : v 2 = t * u 2 := congrArg (fun x : Space => x 2) scaled
    exact (gnomonicNormal_upward q).not_ge (top ▸ mul_nonpos_of_nonpos_of_nonneg
      negative.le (gnomonicNormal_upward p).le)

private theorem minorArcTangent_gnomonic (p q : Plane) (different : p ≠ q) :
    ∃ s : ℝ, 0 < s ∧ minorArcTangent (gnomonicNormal p) (gnomonicNormal q) =
      s • tangentProjection (gnomonicNormal p) (horizontalLift (q - p)) := by
  let n := gnomonicNormal p
  let m := gnomonicNormal q
  let P := tangentProjection n
  have angles := gnomonic_angle_pos_lt_pi different
  have sine : 0 < sin (angle n m) := sin_pos_of_pos_of_lt_pi angles.1 angles.2
  have north (x : Plane) : northLift x = ‖northLift x‖ • gnomonicNormal x :=
    (NormedSpace.norm_smul_normalize _).symm
  have lift : horizontalLift (q - p) = northLift q - northLift p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change (0 : ℝ) = 1 - 1
      norm_num
  have projected : P (horizontalLift (q - p)) = ‖northLift q‖ • P m := by
    calc
      _ = P (northLift q) - P (northLift p) := by rw [lift, map_sub]
      _ = ‖northLift q‖ • P m - ‖northLift p‖ • P n :=
        congrArg₂ (· - ·) ((congrArg P (north q)).trans (P.map_smul _ _))
          ((congrArg P (north p)).trans (P.map_smul _ _))
      _ = _ := by rw [show P n = 0 from tangentProjection_self n (gnomonicNormal_unit p),
        smul_zero, sub_zero]
  have tangent : minorArcTangent n m = (sin (angle n m))⁻¹ • P m := by
    rw [minorArcTangent, show P m = m - inner ℝ n m • n from tangentProjection_apply n m,
      inner_eq_cos_angle_of_norm_eq_one (gnomonicNormal_unit p) (gnomonicNormal_unit q)]
  have q_pos := norm_pos_iff.mpr (northLift_ne_zero q)
  refine ⟨(sin (angle n m))⁻¹ / ‖northLift q‖, div_pos (inv_pos.mpr sine) q_pos, ?_⟩
  rw [projected, tangent, smul_smul, div_mul_cancel₀ _ q_pos.ne']

/-- The spherical half-angle sine at a gnomonic corner is bounded below by
its planar half-angle sine times the height of the unit corner site. -/
theorem sin_half_gnomonic_corner_ge (p q r : Plane) (qp : q ≠ p) (rp : r ≠ p) :
    gnomonicNormal p 2 * sin (angle (q - p) (r - p) / 2) ≤
      sin (angle (minorArcTangent (gnomonicNormal p) (gnomonicNormal q))
        (minorArcTangent (gnomonicNormal p) (gnomonicNormal r)) / 2) := by
  let n := gnomonicNormal p
  let T := (tangentProjection n).comp horizontalLift
  obtain ⟨s, s_pos, first⟩ := minorArcTangent_gnomonic p q qp.symm
  obtain ⟨t, t_pos, second⟩ := minorArcTangent_gnomonic p r rp.symm
  rw [first, second, angle_smul_left_of_pos _ _ s_pos, angle_smul_right_of_pos _ _ t_pos]
  have norms (x : Plane) := norm_tangentProjection_horizontal n (gnomonicNormal_unit p)
    (gnomonicNormal_upward p).le x
  exact sin_half_angle_map_ge T (gnomonicNormal_upward p)
    (fun x => (norms x).1) (fun x => (norms x).2) (sub_ne_zero.mpr qp) (sub_ne_zero.mpr rp)

end Unfoldings.Cap
