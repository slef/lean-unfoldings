module

public import Unfoldings.Cap.GnomonicArea
public import Unfoldings.Geometry.RadialPlaneAngle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Angular distances compare to gnomonic distances by the squared secant factor. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open NormedSpace InnerProductGeometry Real

/-- The straight lifted segment at height one has angular length at most its planar length. -/
theorem angle_gnomonicNormal_le_dist (p q : Plane) :
    angle (gnomonicNormal p) (gnomonicNormal q) ≤ dist p q := by
  let n := EuclideanSpace.basisFun (Fin 3) ℝ (2 : Fin 3)
  have nu : ‖n‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one 2
  have height (x : Plane) : inner ℝ n (northLift x) = 1 := by
    dsimp only [n]
    rw [EuclideanSpace.basisFun_inner, northLift_height]
  have result := angle_normalize_le_div_planeHeight nu zero_lt_one (height p) (height q)
  rw [div_one, ← dist_eq_norm, northLift_isometry.dist_eq, dist_comm] at result
  exact result

private theorem norm_sub_unit_le_angle {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ≤ angle u v := by
  let t := angle u v / 2
  have t_nonnegative : 0 ≤ t := div_nonneg (angle_nonneg _ _) (by norm_num)
  have sine : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi t_nonnegative
    (by dsimp [t]; linarith [angle_le_pi u v, pi_pos])
  have angle_eq : angle u v = 2 * t := by dsimp [t]; ring
  have squared := norm_sub_pow_two_real u v
  rw [hu, hv, inner_eq_cos_angle_of_norm_eq_one hu hv, angle_eq, cos_two_mul] at squared
  have exact_chord : ‖u - v‖ = 2 * sin t :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (by
      nlinarith only [squared, sin_sq_add_cos_sq t])
  rw [exact_chord, angle_eq]
  linarith only [sin_le t_nonnegative]

set_option maxHeartbeats 600000 in
-- Retain the scale factors in the squared chord bound.
/-- The inverse chart is Lipschitz with constant (c^{-2}) on unit normals
at height at least (c). -/
theorem dist_le_inv_sq_mul_gnomonicAngle (p q : Plane) {c : ℝ}
    (cpos : 0 < c) (cle : c ≤ 1) (p_up : c ≤ gnomonicNormal p 2) (q_up : c ≤ gnomonicNormal q 2) :
    dist p q ≤ (c ^ 2)⁻¹ * angle (gnomonicNormal p) (gnomonicNormal q) := by
  let n := EuclideanSpace.basisFun (Fin 3) ℝ (2 : Fin 3)
  have nu : ‖n‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one 2
  let X := c • northLift p
  let Y := c • northLift q
  have height (z : Plane) : inner ℝ n (c • northLift z) = c := by
    rw [real_inner_smul_right]
    change c * inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ 2) (northLift z) = c
    rw [EuclideanSpace.basisFun_inner, northLift_height, mul_one]
  have scaled (z : Plane) (up : c ≤ gnomonicNormal z 2) : ‖c • northLift z‖ ≤ 1 := by
    have eq : gnomonicNormal z 2 = ‖northLift z‖⁻¹ := by
      change ‖northLift z‖⁻¹ * 1 = _
      rw [mul_one]
    rw [eq, inv_eq_one_div] at up
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos cpos, ← le_div_iff₀
      (norm_pos_iff.mpr (northLift_ne_zero z))]
    exact up
  have first := (normalized_chord_sq_bounds nu (height p) (height q)
    (scaled p p_up) (scaled q q_up) cpos cle).1
  have prod : ‖X‖ * ‖Y‖ ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul (scaled p p_up) (scaled q q_up) (norm_nonneg Y) zero_le_one
  change c ^ 2 * ‖X - Y‖ ^ 2 ≤ ‖X‖ * ‖Y‖ *
    ‖NormedSpace.normalize X - NormedSpace.normalize Y‖ ^ 2 at first
  have upper := first.trans (mul_le_mul_of_nonneg_right prod (sq_nonneg
    ‖NormedSpace.normalize X - NormedSpace.normalize Y‖))
  have difference : X - Y = c • (northLift p - northLift q) := (smul_sub _ _ _).symm
  have nx : NormedSpace.normalize X = gnomonicNormal p := by
    dsimp only [X, gnomonicNormal]
    rw [normalize_smul_of_pos cpos]
  have ny : NormedSpace.normalize Y = gnomonicNormal q := by
    dsimp only [Y, gnomonicNormal]
    rw [normalize_smul_of_pos cpos]
  rw [one_mul, difference, norm_smul, Real.norm_eq_abs, abs_of_pos cpos, nx, ny,
    ← dist_eq_norm, northLift_isometry.dist_eq, ← dist_eq_norm] at upper
  have squared : (c ^ 2 * dist p q) ^ 2 ≤
      dist (gnomonicNormal p) (gnomonicNormal q) ^ 2 := by
    convert upper using 1
    ring
  have chord := (sq_le_sq₀ (by positivity) dist_nonneg).mp squared
  have angular := norm_sub_unit_le_angle (gnomonicNormal_unit p) (gnomonicNormal_unit q)
  rw [← dist_eq_norm] at angular
  rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos cpos 2), mul_comm]
  exact chord.trans angular

end Unfoldings.Cap
