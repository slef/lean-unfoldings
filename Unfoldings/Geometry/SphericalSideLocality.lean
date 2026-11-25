module

public import Unfoldings.Geometry.SphericalEndpointLocality
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Distance to an incident side uses the full corner angle, capped at a right angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For an obtuse corner the closest point of the other ray is the common
endpoint. For an acute corner we may use the distance to its supporting line. -/
theorem sine_capped_angle_mul_le_norm_sub {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * sin (min (angle u v) (π / 2)) ≤ ‖a • u - b • v‖ := by
  let θ := angle u v
  have chord := norm_sub_pow_two_real (a • u) (b • v)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hu, hv,
    mul_one, mul_one, real_inner_smul_left, real_inner_smul_right,
    inner_eq_cos_angle_of_norm_eq_one hu hv] at chord
  have θ_nonneg : 0 ≤ θ := angle_nonneg _ _
  have θ_le : θ ≤ π := angle_le_pi _ _
  have sine : 0 ≤ sin (min θ (π / 2)) :=
    sin_nonneg_of_nonneg_of_le_pi (le_min θ_nonneg (by positivity))
      ((min_le_left _ _).trans θ_le)
  apply (sq_le_sq₀ (mul_nonneg ha sine) (norm_nonneg _)).mp
  rw [chord]
  change (a * sin (min θ (π / 2))) ^ 2 ≤ a ^ 2 - 2 * (a * (b * cos θ)) + b ^ 2
  rcases le_total θ (π / 2) with acute | obtuse
  · rw [min_eq_left acute]
    have circle := congrArg (fun t : ℝ => a ^ 2 * t) (sin_sq_add_cos_sq θ)
    nlinarith only [circle, sq_nonneg (b - a * cos θ)]
  · rw [min_eq_right obtuse, sin_pi_div_two]
    have negative := cos_nonpos_of_pi_div_two_le_of_le obtuse (by linarith only [θ_le, pi_pos])
    nlinarith only [sq_nonneg b, mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) negative]

private theorem chord_sine_lower {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (bound : a ≤ L)
    (small : L ≤ π / 2) : (sin L / L) * a ≤ sin a := by
  have t : 0 ≤ a / L := div_nonneg ha hL.le
  have t_le : a / L ≤ 1 := (div_le_one₀ hL).2 bound
  have concave := strictConcaveOn_sin_Icc.concaveOn.2
    (show L ∈ Set.Icc 0 π from ⟨hL.le, by linarith only [small, pi_pos]⟩)
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    t (sub_nonneg.mpr t_le) (by ring)
  simp only [smul_eq_mul, sin_zero, mul_zero, add_zero, div_mul_cancel₀ _ hL.ne'] at concave
  calc
    _ = (a / L) * sin L := by ring
    _ ≤ _ := concave

/-- A crossing far from a shared endpoint excludes a hit on the incident side.
The factor retains both the actual side-length bound and the actual corner angle. -/
theorem greatCirclePoint_incident_side_bound {origin u v : E}
    (ho : ‖origin‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (u_tangent : inner ℝ origin u = 0) (v_tangent : inner ℝ origin v = 0)
    {a b L ψ : ℝ} (ha : 0 ≤ a) (a_le : a ≤ L) (L_pos : 0 < L) (L_small : L ≤ π / 2)
    (hb : 0 ≤ b) (b_small : b ≤ π / 2) (ψ_pos : 0 < ψ) (ψ_le : ψ ≤ angle u v) :
    a ≤ L / (sin L * sin (min ψ (π / 2))) *
      angle (greatCirclePoint origin u a) (greatCirclePoint origin v b) := by
  let x := greatCirclePoint origin u a
  let y := greatCirclePoint origin v b
  let D := sin a • u - sin b • v
  have orthogonal : inner ℝ ((cos a - cos b) • origin) D = 0 := by
    rw [real_inner_smul_left]
    dsimp only [D]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, u_tangent, v_tangent]
    ring
  have displacement : x - y = (cos a - cos b) • origin + D := by
    dsimp only [x, y, greatCirclePoint, D]
    rw [sub_smul]
    abel
  have projected : ‖D‖ ≤ ‖x - y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [displacement, norm_add_pow_two_real, orthogonal]
    linarith only [sq_nonneg ‖(cos a - cos b) • origin‖]
  have sL_pos := sin_pos_of_pos_of_lt_pi L_pos (L_small.trans_lt (by linarith only [pi_pos]))
  have sine : 0 < sin (min ψ (π / 2)) := sin_pos_of_pos_of_lt_pi
    (lt_min ψ_pos (by positivity)) ((min_le_right _ _).trans_lt (by linarith only [pi_pos]))
  have sine_order : sin (min ψ (π / 2)) ≤ sin (min (angle u v) (π / 2)) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith only [lt_min ψ_pos pi_div_two_pos, pi_pos])
      (min_le_right _ _) (min_le_min_right _ ψ_le)
  have sa := sin_nonneg_of_nonneg_of_le_pi ha (by linarith only [a_le, L_small, pi_pos])
  have sb := sin_nonneg_of_nonneg_of_le_pi hb (by linarith only [b_small, pi_pos])
  have exact_bound : ((sin L / L) * a) * sin (min ψ (π / 2)) ≤ angle x y := calc
    _ ≤ sin a * sin (min ψ (π / 2)) :=
      mul_le_mul_of_nonneg_right (chord_sine_lower ha L_pos a_le L_small) sine.le
    _ ≤ sin a * sin (min (angle u v) (π / 2)) :=
      mul_le_mul_of_nonneg_left sine_order sa
    _ ≤ ‖D‖ := sine_capped_angle_mul_le_norm_sub hu hv sa sb
    _ ≤ ‖x - y‖ := projected
    _ ≤ _ := norm_sub_le_angle_of_unit (norm_greatCirclePoint ho hu u_tangent a)
      (norm_greatCirclePoint ho hv v_tangent b)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos sL_pos sine)).mpr
  have scaled := mul_le_mul_of_nonneg_right exact_bound L_pos.le
  field_simp at scaled
  nlinarith only [scaled]

end Unfoldings
