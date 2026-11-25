module

public import Unfoldings.Cap.SectionAngles
public import Unfoldings.Geometry.StraightHingeTurn
public import Unfoldings.Geometry.LineTransverse

/-! The sharp hinge estimate for directions in any two spatial support planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry Real

private theorem plane_norm_sq_coord (v : Plane) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem plane_inner_coord (u v : Plane) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem plane_unit_sq {u : Plane} (unit : ‖u‖ = 1) :
    u 0 ^ 2 + u 1 ^ 2 = 1 := by
  rw [← plane_norm_sq_coord, unit, one_pow]

private theorem norm_sq_from_parallel_perp {u : Plane} (unit : ‖u‖ = 1) (w : Plane) :
    inner ℝ u w ^ 2 + orient 0 u w ^ 2 = ‖w‖ ^ 2 := by
  rw [plane_inner_coord, plane_norm_sq_coord]
  simp only [orient, PiLp.zero_apply, sub_zero]
  linear_combination (w 0 ^ 2 + w 1 ^ 2) * plane_unit_sq unit

private theorem parallel_perp_decomposition {u : Plane} (unit : ‖u‖ = 1) (w : Plane) :
    (inner ℝ u w) • u + (orient 0 u w) • (WithLp.toLp 2 ![-u 1, u 0] : Plane) = w := by
  ext k
  fin_cases k
  · change inner ℝ u w * u 0 + orient 0 u w * (-u 1) = w 0
    rw [plane_inner_coord]
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination w 0 * plane_unit_sq unit
  · change inner ℝ u w * u 1 + orient 0 u w * u 0 = w 1
    rw [plane_inner_coord]
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination w 1 * plane_unit_sq unit

/-- The crease cosine in a unit section direction and its perpendicular
matches the cosine of the two actual lifted spatial vectors. -/
theorem angle_horizontalAtHeight_eq_straightHingeAngle {u : Plane} (unit : ‖u‖ = 1)
    (w : Plane) (c p : ℝ) :
    angle (horizontalAtHeight w c) (horizontalAtHeight u p) =
      straightHingeAngle (inner ℝ u w) (orient 0 u w) c p := by
  have nw : ‖horizontalAtHeight w c‖ = sqrt (‖w‖ ^ 2 + c ^ 2) := by
    have h := horizontal_norm_sq (horizontalAtHeight w c)
    rw [horizontal_horizontalAtHeight, height_horizontalAtHeight] at h
    rw [← h, sqrt_sq (norm_nonneg _)]
  have nu : ‖horizontalAtHeight u p‖ = sqrt (1 + p ^ 2) := by
    have h := horizontal_norm_sq (horizontalAtHeight u p)
    rw [horizontal_horizontalAtHeight, height_horizontalAtHeight, unit, one_pow] at h
    rw [← h, sqrt_sq (norm_nonneg _)]
  rw [angle, straightHingeAngle, straightHingeCos, nw, nu, norm_sq_from_parallel_perp unit,
    horizontal_inner, horizontal_horizontalAtHeight, horizontal_horizontalAtHeight,
    height_horizontalAtHeight, height_horizontalAtHeight, real_inner_comm u w]

/-- A straight lifted hinge on two support planes pays at most the sine of the tilt
times the change of spatial section inclination. The interface uses just the plane slopes. -/
theorem abs_sectionAngle_sub_le_sin_tilt {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2)
    (l r w d : Plane) (left_bound : ‖l‖ ≤ tan phi) (right_bound : ‖r‖ ≤ tan phi)
    (common : inner ℝ l w = inner ℝ r w) (unit : ‖d‖ = 1) (transverse : orient 0 w d ≠ 0) :
    let e := horizontalAtHeight w (-inner ℝ l w)
    let a := horizontalAtHeight d (-inner ℝ l d)
    let b := horizontalAtHeight d (-inner ℝ r d)
    |angle e a - angle e b| ≤ sin phi * angle a b := by
  let a := inner ℝ d w
  let b := orient 0 d w
  let c := -inner ℝ l w
  let u : Plane := WithLp.toLp 2 ![-d 1, d 0]
  let p (f : Plane) := -inner ℝ f d
  let q (f : Plane) := -inner ℝ f u
  have bne : b ≠ 0 := by
    intro zero
    apply transverse
    change orient 0 w d = 0
    change orient 0 d w = 0 at zero
    simp only [orient, PiLp.zero_apply, sub_zero] at zero ⊢
    linarith only [zero]
  have support (f : Plane) (bounded : ‖f‖ ≤ tan phi) (shared : -inner ℝ f w = c) :
      p f ^ 2 + straightHingeTransverse a b c (p f) ^ 2 ≤ tan phi ^ 2 := by
    have slope : c = a * p f + b * q f := by
      rw [← shared]
      conv_lhs => rw [← Cap.parallel_perp_decomposition unit w]
      simp only [inner_add_right, real_inner_smul_right, p, q, a, b, u]
      ring
    have eq : straightHingeTransverse a b c (p f) = q f := by
      unfold straightHingeTransverse
      apply (div_eq_iff bne).mpr
      linarith only [slope]
    have q_form : q f = orient 0 d (-f) := by
      simp only [q, Cap.plane_inner_coord, orient, PiLp.zero_apply, PiLp.neg_apply, sub_zero]
      change -(f 0 * (-d 1) + f 1 * d 0) = _
      ring
    have p_form : p f = inner ℝ d (-f) := by
      change -inner ℝ f d = _
      rw [inner_neg_right, real_inner_comm f d]
    rw [eq, p_form, q_form, Cap.norm_sq_from_parallel_perp unit, norm_neg]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans bounded)).mpr bounded
  have angle_eq (f : Plane) :
      angle (horizontalAtHeight w c) (horizontalAtHeight d (p f)) =
        straightHingeAngle a b c (p f) :=
    angle_horizontalAtHeight_eq_straightHingeAngle unit w _ _
  change |angle (horizontalAtHeight w c) (horizontalAtHeight d (p l)) -
    angle (horizontalAtHeight w c) (horizontalAtHeight d (p r))| ≤
    sin phi * angle (horizontalAtHeight d (p l)) (horizontalAtHeight d (p r))
  rw [angle_eq l, angle_eq r, angle_horizontalAtHeight d unit]
  exact abs_straightHingeAngle_sub_le_sin_abs bne nonnegative small (support r right_bound (congrArg Neg.neg common.symm))
    (support l left_bound rfl) |>.trans_eq (congrArg (sin phi * ·) (abs_sub_comm _ _))

end Unfoldings.Cap
