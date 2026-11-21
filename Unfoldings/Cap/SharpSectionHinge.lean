module

public import Unfoldings.Cap.SeamDirections
public import Unfoldings.Geometry.StraightHingeTurn

/-! Sharp tilt factor for the actual seam-relative angles of a cap section. -/

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

end Unfoldings.Cap

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The change of angle to a shared tangent direction is at most the
extrinsic section bend multiplied by the sine of the cap tilt. -/
theorem abs_spatialDirection_common_angle_sub_le_sin_tilt
    {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (l r : Face) (w d : Plane) (common : K.spatialDirection l w = K.spatialDirection r w)
    (unit : ‖d‖ = 1) (transverse : orient 0 w d ≠ 0) :
    let e := K.spatialDirection l w
    |angle e (K.spatialDirection l d) - angle e (K.spatialDirection r d)| ≤
      sin phi * angle (K.spatialDirection l d) (K.spatialDirection r d) := by
  let a := inner ℝ d w
  let b := orient 0 d w
  let c := (K.spatialDirection l w) 2
  let u : Plane := WithLp.toLp 2 ![-d 1, d 0]
  let p (f : Face) := -inner ℝ (K.normalSlope f) d
  let q (f : Face) := -inner ℝ (K.normalSlope f) u
  have bne : b ≠ 0 := by
    intro zero
    apply transverse
    change orient 0 w d = 0
    change orient 0 d w = 0 at zero
    simp only [orient, PiLp.zero_apply, sub_zero] at zero ⊢
    linarith only [zero]
  have support (f : Face) (shared : (K.spatialDirection f w) 2 = c) :
      p f ^ 2 + straightHingeTransverse a b c (p f) ^ 2 ≤ tan phi ^ 2 := by
    have slope : c = a * p f + b * q f := by
      rw [← shared, K.spatialDirection_height]
      conv_lhs => rw [← Cap.parallel_perp_decomposition unit w]
      simp only [inner_add_right, real_inner_smul_right, p, q, a, b, u]
      ring
    have eq : straightHingeTransverse a b c (p f) = q f := by
      unfold straightHingeTransverse
      apply (div_eq_iff bne).mpr
      linarith only [slope]
    have q_form : q f = orient 0 d (-K.normalSlope f) := by
      simp only [q, Cap.plane_inner_coord, orient, PiLp.zero_apply, PiLp.neg_apply, sub_zero]
      change -((K.normalSlope f) 0 * (-d 1) + (K.normalSlope f) 1 * d 0) = _
      ring
    have p_form : p f = inner ℝ d (-K.normalSlope f) := by
      change -inner ℝ (K.normalSlope f) d = _
      rw [inner_neg_right, real_inner_comm (K.normalSlope f) d]
    rw [eq, p_form, q_form, Cap.norm_sq_from_parallel_perp unit, norm_neg]
    have cn : 0 < cos phi := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], small⟩
    have bound := K.normalSlope_norm_le cn tilt f
    rw [← sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith [pi_pos]),
      ← tan_eq_sin_div_cos] at bound
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans bound)).mpr bound
  have angle_eq (f : Face) :
      angle (K.spatialDirection l w) (K.spatialDirection f d) =
        straightHingeAngle a b c (p f) := by
    rw [K.spatialDirection_eq_section l w, K.spatialDirection_eq_section f d]
    have hc : c = -inner ℝ (K.normalSlope l) w := K.spatialDirection_height l w
    rw [hc]
    exact Cap.angle_horizontalAtHeight_eq_straightHingeAngle unit w _ _
  have right_height : (K.spatialDirection r w) 2 = c :=
    congrArg (fun x : Space => x 2) common.symm
  change |angle (K.spatialDirection l w) (K.spatialDirection l d) -
    angle (K.spatialDirection l w) (K.spatialDirection r d)| ≤
    sin phi * angle (K.spatialDirection l d) (K.spatialDirection r d)
  rw [angle_eq l, angle_eq r, K.spatialDirection_angle l r d unit]
  exact abs_straightHingeAngle_sub_le_sin_abs bne nonnegative small (support r right_height)
    (support l rfl) |>.trans_eq (congrArg (sin phi * ·) (abs_sub_comm _ _))

/-- The same estimate applies to the genuine tangent along any seam. -/
theorem abs_spatialDirection_seam_angle_sub_le_sin_tilt
    {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (s : C.Seam) (d : Plane) (unit : ‖d‖ = 1)
    (transverse : orient 0 (K.projectedSeamVector s) d ≠ 0) :
    let e := K.spatialDirection (C.left s).face (K.projectedSeamVector s)
    |angle e (K.spatialDirection (C.left s).face d) -
      angle e (K.spatialDirection (C.right s).face d)| ≤
      sin phi * angle (K.spatialDirection (C.left s).face d)
        (K.spatialDirection (C.right s).face d) :=
  K.abs_spatialDirection_common_angle_sub_le_sin_tilt nonnegative small tilt
    (C.left s).face (C.right s).face (K.projectedSeamVector s) d
    (K.spatialDirection_seam s) unit transverse

/-- The shared-tangent estimate is invariant under positive rescaling of the
transverse direction. -/
theorem abs_spatialDirection_common_angle_sub_le_sin_tilt_of_transverse
    {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (l r : Face) (w d : Plane) (common : K.spatialDirection l w = K.spatialDirection r w)
    (transverse : orient 0 w d ≠ 0) :
    let e := K.spatialDirection l w
    |angle e (K.spatialDirection l d) - angle e (K.spatialDirection r d)| ≤
      sin phi * angle (K.spatialDirection l d) (K.spatialDirection r d) := by
  have nonzero : d ≠ 0 := by
    intro h
    apply transverse
    simp [h, orient]
  let u := NormedSpace.normalize d
  have unit : ‖u‖ = 1 := NormedSpace.norm_normalize nonzero
  have positive : 0 < ‖d‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr nonzero)
  have side : orient 0 (w) u ≠ 0 := by
    have eq : orient 0 (w) u =
        ‖d‖⁻¹ * orient 0 (w) d := by
      simp only [u, NormedSpace.normalize, orient, PiLp.smul_apply, smul_eq_mul,
        PiLp.zero_apply, sub_zero]
      ring
    rw [eq]
    exact mul_ne_zero positive.ne' transverse
  have map (f : Face) : K.spatialDirection f u = ‖d‖⁻¹ • K.spatialDirection f d := by
    simp only [u, NormedSpace.normalize, spatialDirection, pullbackDirection, map_smul]
  have bound := K.abs_spatialDirection_common_angle_sub_le_sin_tilt nonnegative small tilt
    l r w u common unit side
  dsimp only at bound ⊢
  simpa only [map, angle_smul_left_of_pos _ _ positive, angle_smul_right_of_pos _ _ positive]
    using bound

/-- The same sharp hinge bound needs only a transverse projected direction. -/
theorem abs_spatialDirection_seam_angle_sub_le_sin_tilt_of_transverse
    {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (s : C.Seam) (d : Plane) (transverse : orient 0 (K.projectedSeamVector s) d ≠ 0) :
    let e := K.spatialDirection (C.left s).face (K.projectedSeamVector s)
    |angle e (K.spatialDirection (C.left s).face d) -
      angle e (K.spatialDirection (C.right s).face d)| ≤
      sin phi * angle (K.spatialDirection (C.left s).face d)
        (K.spatialDirection (C.right s).face d) :=
  K.abs_spatialDirection_common_angle_sub_le_sin_tilt_of_transverse nonnegative small tilt
    (C.left s).face (C.right s).face (K.projectedSeamVector s) d
    (K.spatialDirection_seam s) transverse

end Unfoldings.ConvexCap
