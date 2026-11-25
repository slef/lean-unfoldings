module

public import Unfoldings.Roof.ActiveClosingVariation
public import Unfoldings.Roof.GermSupports
public import Unfoldings.Geometry.SpatialStraightHinge
public import Unfoldings.Cap.SharpAngleProjection

/-! Sharp angular estimates for the actual support directions of any convex roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The slope lift agrees with the original face placement after inverse projection. -/
theorem sectionDirection_eq_place_linear (f : Face) (d : Plane) :
    K.sectionDirection f d = (K.folding.place f).linear ((K.projectFaceEquiv f).linear.symm d) := by
  let w := (K.folding.place f).linear ((K.projectFaceEquiv f).linear.symm d)
  have projected : Cap.horizontal w = d :=
    (K.projectFaceEquiv f).linear.apply_symm_apply d
  have tangent : inner ℝ (K.normal f) w = 0 :=
    K.normal_tangent f ((K.projectFaceEquiv f).linear.symm d)
  have height := K.normalSlope_inner_add_height f w
  rw [projected, tangent, mul_zero] at height
  ext i
  fin_cases i
  · exact (congrArg (fun p : Plane => p 0) projected).symm
  · exact (congrArg (fun p : Plane => p 1) projected).symm
  · change -inner ℝ (K.normalSlope f) d = w 2
    linarith only [height]

@[simp] theorem horizontal_sectionDirection (f : Face) (d : Plane) :
    Cap.horizontal (K.sectionDirection f d) = d :=
  Cap.horizontal_horizontalAtHeight _ _

theorem sectionDirection_ne_zero (f : Face) {d : Plane} (different : d ≠ 0) :
    K.sectionDirection f d ≠ 0 := fun zero =>
  different ((K.horizontal_sectionDirection f d).symm.trans (by rw [zero, map_zero]))

theorem sectionDirection_tangent (f : Face) (d : Plane) :
    inner ℝ (K.normal f) (K.sectionDirection f d) = 0 := by
  rw [K.sectionDirection_eq_place_linear]
  exact K.normal_tangent f _

theorem sectionDirection_smul (f : Face) (t : ℝ) (d : Plane) :
    K.sectionDirection f (t • d) = t • K.sectionDirection f d := by
  simp only [K.sectionDirection_eq_place_linear, map_smul]

theorem sectionDirection_neg (f : Face) (d : Plane) :
    K.sectionDirection f (-d) = -K.sectionDirection f d := by
  simp only [K.sectionDirection_eq_place_linear, map_neg]

/-- An original incident germ is the section lift of its projected ray. -/
theorem sectionDirection_horizontal_germ (p : C.Germ) :
    K.sectionDirection p.1.1 (Cap.horizontal (K.folding.germDirection p)) =
      K.folding.germDirection p := by
  unfold SpatialFolding.germDirection SpatialFolding.germFarPoint
  rw [map_sub, sectionDirection_eq_place_linear]
  let f := p.1.1
  have projection (a b : Plane) :
      (K.projectFaceEquiv f).linear (b - a) = K.projectFace f b - K.projectFace f a :=
    (K.projectFaceEquiv f).toAffineMap.linear_apply_vsub b a
  let a := (C.triangle f).vertex p.1.2
  let b := (C.triangle f).vertex (C.germFarCorner p).2
  change (K.folding.place f).linear ((K.projectFaceEquiv f).linear.symm
    (K.projectFace f b - K.projectFace f a)) = K.folding.place f b - K.folding.place f a
  rw [← projection, LinearEquiv.symm_apply_apply]
  exact (K.folding.place f).toAffineMap.linear_apply_vsub b a

theorem normalSlope_norm_le_tan {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2)
    (tilt : K.TiltBound φ) (f : Face) : ‖K.normalSlope f‖ ≤ tan φ := by
  have cp := cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos], small⟩
  have bound := K.normalSlope_norm_le cp tilt f
  rwa [← sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith only [small, pi_pos]),
    ← tan_eq_sin_div_cos] at bound

/-- A true crease contact on a straight connector pays only the sine-scaled change
of its actual plane inclinations. -/
theorem abs_sectionDirection_common_angle_sub_le_sin_tilt {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (l r : Face) (w d : Plane) (common : K.sectionDirection l w = K.sectionDirection r w)
    (transverse : orient 0 w d ≠ 0) :
    let e := K.sectionDirection l w
    |angle e (K.sectionDirection l d) - angle e (K.sectionDirection r d)| ≤
      sin φ * angle (K.sectionDirection l d) (K.sectionDirection r d) := by
  have agree : inner ℝ (K.normalSlope l) w = inner ℝ (K.normalSlope r) w :=
    neg_inj.mp (congrArg (fun x : Space => x 2) common)
  have nonzero : d ≠ 0 := by
    intro zero
    apply transverse
    simp [zero, orient]
  let u := NormedSpace.normalize d
  have unit : ‖u‖ = 1 := NormedSpace.norm_normalize nonzero
  have positive := inv_pos.mpr (norm_pos_iff.mpr nonzero)
  have across : orient 0 w u ≠ 0 := by
    have eq : orient 0 w u = ‖d‖⁻¹ * orient 0 w d := by
      simp only [u, NormedSpace.normalize, orient, PiLp.smul_apply, smul_eq_mul,
        PiLp.zero_apply, sub_zero]
      ring
    rw [eq]
    exact mul_ne_zero positive.ne' transverse
  have sharp := Cap.abs_sectionAngle_sub_le_sin_tilt nonnegative small
    (K.normalSlope l) (K.normalSlope r) w u (K.normalSlope_norm_le_tan nonnegative small tilt l)
    (K.normalSlope_norm_le_tan nonnegative small tilt r) agree unit across
  change |angle (K.sectionDirection l w) (K.sectionDirection l u) -
    angle (K.sectionDirection l w) (K.sectionDirection r u)| ≤
    sin φ * angle (K.sectionDirection l u) (K.sectionDirection r u) at sharp
  simpa only [u, NormedSpace.normalize, K.sectionDirection_smul,
    angle_smul_left_of_pos _ _ positive, angle_smul_right_of_pos _ _ positive] using sharp

/-- Both endpoint directions of a corner lying in one actual support plane pay a
single sharp projected-angle error. -/
theorem abs_sectionDirection_angle_error_le_sharp {φ : ℝ} (nonnegative : 0 ≤ φ)
    (small : φ < π / 2) (tilt : K.TiltBound φ) (f : Face) {a b : Plane}
    (ane : a ≠ 0) (bne : b ≠ 0) :
    |angle (K.sectionDirection f a) (K.sectionDirection f b) - angle a b| ≤
      2 * arcsin (tan (φ / 2) ^ 2) := by
  have cp := cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos], small⟩
  have err := Cap.tangent_projection_angle_error (K.normal_unit f) cp (tilt f)
    (K.sectionDirection_ne_zero f ane) (K.sectionDirection_ne_zero f bne)
    (K.sectionDirection_tangent f a) (K.sectionDirection_tangent f b)
  have half_tan : (1 - cos φ) / (1 + cos φ) = tan (φ / 2) ^ 2 := by
    have ct : 0 < 1 + tan (φ / 2) ^ 2 := by positivity
    have identity := (eq_div_iff ct.ne').mp
      (cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq φ (by linarith only [cp]))
    exact (div_eq_iff (by positivity : 0 < 1 + cos φ).ne').mpr (by linarith only [identity])
  rwa [K.horizontal_sectionDirection, K.horizontal_sectionDirection, abs_sub_comm, half_tan] at err

end Unfoldings.ConvexRoof
