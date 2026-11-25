module

public import Unfoldings.Cap.SeamDirections
public import Unfoldings.Geometry.SpatialStraightHinge

/-! Sharp tilt factor for the actual seam-relative angles of a cap section. -/

@[expose] public section

noncomputable section

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
  have positive : 0 < cos phi := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], small⟩
  have bounded (f : Face) : ‖K.normalSlope f‖ ≤ tan phi := by
    have h := K.normalSlope_norm_le positive tilt f
    rw [← sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith [pi_pos]),
      ← tan_eq_sin_div_cos] at h
    exact h
  have agree : inner ℝ (K.normalSlope l) w = inner ℝ (K.normalSlope r) w :=
    neg_inj.mp ((K.spatialDirection_height l w).symm.trans
      ((congrArg (fun x : Space => x 2) common).trans (K.spatialDirection_height r w)))
  simpa only [K.spatialDirection_eq_section] using Cap.abs_sectionAngle_sub_le_sin_tilt
    nonnegative small (K.normalSlope l) (K.normalSlope r) w d (bounded l) (bounded r)
    agree unit transverse

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
