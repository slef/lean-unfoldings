module

public import Unfoldings.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative localization at the common endpoint of incident spherical edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The chord between two points of a unit sphere is at most their angular distance. -/
theorem norm_sub_le_angle_of_unit {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ≤ angle x y := by
  have chord := norm_sub_pow_two_real x y
  rw [hx, hy, inner_eq_cos_angle_of_norm_eq_one hx hy] at chord
  have square : ‖x - y‖ ^ 2 ≤ angle x y ^ 2 := by
    linarith [one_sub_sq_div_two_le_cos (x := angle x y)]
  exact (sq_le_sq₀ (norm_nonneg _) (angle_nonneg _ _)).mp square

/-- Chords across two rays have a lower bound in terms of their incident angle. -/
theorem sin_half_angle_mul_add_le_norm_sub {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sin (angle u v / 2) * (a + b) ≤ ‖a • u - b • v‖ := by
  have chord := norm_sub_pow_two_real (a • u) (b • v)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hu, hv, mul_one,
    mul_one, real_inner_smul_left, real_inner_smul_right,
    inner_eq_cos_angle_of_norm_eq_one hu hv] at chord
  have half_sq : cos (angle u v) = 1 - 2 * sin (angle u v / 2) ^ 2 := by
    nth_rw 1 [show angle u v = 2 * (angle u v / 2) by ring]
    exact cos_two_mul_eq_one_sub _
  have identity : ‖a • u - b • v‖ ^ 2 =
      (sin (angle u v / 2) * (a + b)) ^ 2 + cos (angle u v / 2) ^ 2 * (a - b) ^ 2 := by
    rw [chord, half_sq]
    have cos_sq : cos (angle u v / 2) ^ 2 = 1 - sin (angle u v / 2) ^ 2 := by
      linarith [sin_sq_add_cos_sq (angle u v / 2)]
    rw [cos_sq]
    ring
  have sine : 0 ≤ sin (angle u v / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [angle_nonneg u v])
      (by linarith [angle_le_pi u v, pi_pos])
  apply (sq_le_sq₀ (mul_nonneg sine (add_nonneg ha hb)) (norm_nonneg _)).mp
  rw [identity]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The arclength parameterization of the great circle issued from a point and unit tangent. -/
def greatCirclePoint (origin tangent : E) (distance : ℝ) : E :=
  cos distance • origin + sin distance • tangent

theorem norm_greatCirclePoint {origin tangent : E} (unit_origin : ‖origin‖ = 1)
    (unit_tangent : ‖tangent‖ = 1) (tangent_at : inner ℝ origin tangent = 0) (distance : ℝ) :
    ‖greatCirclePoint origin tangent distance‖ = 1 := by
  have square : ‖greatCirclePoint origin tangent distance‖ ^ 2 = 1 := by
    rw [greatCirclePoint, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      unit_origin, unit_tangent, tangent_at,
      show inner ℝ tangent origin = 0 from (real_inner_comm origin tangent).trans tangent_at]
    nlinarith [sin_sq_add_cos_sq distance]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using square)

theorem angle_greatCirclePoint {origin tangent : E} (unit_origin : ‖origin‖ = 1)
    (unit_tangent : ‖tangent‖ = 1) (tangent_at : inner ℝ origin tangent = 0)
    {distance : ℝ} (nonnegative : 0 ≤ distance) (small : distance ≤ π) :
    angle origin (greatCirclePoint origin tangent distance) = distance := by
  have cosine := inner_eq_cos_angle_of_norm_eq_one unit_origin
    (norm_greatCirclePoint unit_origin unit_tangent tangent_at distance)
  rw [greatCirclePoint, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unit_origin, tangent_at] at cosine
  have equal : cos distance = cos (angle origin (greatCirclePoint origin tangent distance)) := by
    simpa [greatCirclePoint] using cosine
  have arccos := congrArg arccos equal
  rwa [arccos_cos nonnegative small, arccos_cos (angle_nonneg _ _) (angle_le_pi _ _), eq_comm]
    at arccos

/-- A point on one short incident spherical edge is close to its common endpoint
if it is close to a point on the other edge. This is the localized count's scale factor. -/
theorem greatCirclePoint_endpoint_distance_le {origin u v : E} (ho : ‖origin‖ = 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (tangent_u : inner ℝ origin u = 0)
    (tangent_v : inner ℝ origin v = 0) {a b ψ : ℝ} (ha : 0 ≤ a) (ha' : a ≤ π / 2)
    (hb : 0 ≤ b) (hb' : b ≤ π / 2) (incident_pos : 0 < ψ) (incident : ψ ≤ angle u v) :
    a ≤ π / (2 * sin (ψ / 2)) *
      angle (greatCirclePoint origin u a) (greatCirclePoint origin v b) := by
  let x := greatCirclePoint origin u a
  let y := greatCirclePoint origin v b
  let D := sin a • u - sin b • v
  have orthogonal : inner ℝ ((cos a - cos b) • origin) D = 0 := by
    rw [real_inner_smul_left]
    dsimp [D]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, tangent_u, tangent_v]
    ring
  have displacement : x - y = (cos a - cos b) • origin + D := by
    dsimp [x, y, greatCirclePoint, D]
    rw [sub_smul]
    abel
  have projected : ‖D‖ ≤ ‖x - y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [displacement, norm_add_pow_two_real, orthogonal]
    linarith [sq_nonneg ‖(cos a - cos b) • origin‖]
  have ψ_le_pi := incident.trans (angle_le_pi _ _)
  have sine : 0 < sin (ψ / 2) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have sine_le : sin (ψ / 2) ≤ sin (angle u v / 2) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos])
      (by linarith [angle_le_pi u v]) (by linarith)
  have sa := sin_nonneg_of_nonneg_of_le_pi ha (by linarith [pi_pos])
  have sb := sin_nonneg_of_nonneg_of_le_pi hb (by linarith [pi_pos])
  have short := sin_half_angle_mul_add_le_norm_sub hu hv sa sb
  have bound : sin (ψ / 2) * (2 / π * a) ≤ angle x y := calc
    _ ≤ sin (ψ / 2) * (sin a + sin b) :=
      mul_le_mul_of_nonneg_left ((mul_le_sin ha ha').trans (le_add_of_nonneg_right sb)) sine.le
    _ ≤ sin (angle u v / 2) * (sin a + sin b) :=
      mul_le_mul_of_nonneg_right sine_le (add_nonneg sa sb)
    _ ≤ ‖D‖ := short
    _ ≤ ‖x - y‖ := projected
    _ ≤ angle x y := norm_sub_le_angle_of_unit (norm_greatCirclePoint ho hu tangent_u a)
      (norm_greatCirclePoint ho hv tangent_v b)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * sin (ψ / 2))).mpr
  have scaled := mul_le_mul_of_nonneg_right bound pi_pos.le
  field_simp at scaled
  nlinarith

end Unfoldings
