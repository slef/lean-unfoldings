module

public import Unfoldings.Geometry.RadialRayProgress

/-! Match perturbed banks at equal source radii using the actual Lipschitz radial inverse. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- A matched-point error becomes an equal-circle contact error. The factor is independent
of the number of original edges, and the contact is the actual bank point. -/
theorem radial_contact_error {K : ℝ≥0}
    (inverse : LipschitzWith K (R.radialPoint outward nonzero))
    {ε : ℝ} (nonnegative : 0 ≤ ε) (small : ε < 1) {x z : ℂ}
    (member : x ∈ R.carrier) (error : ‖z - x‖ ≤ ε * ‖x - R.start‖)
    (r : ℝ≥0) (radius : ‖z - R.start‖ = (r : ℝ)) :
    ‖z - R.radialPoint outward nonzero r‖ ≤
      ((1 + (K : ℝ)) * ε / (1 - ε)) * (r : ℝ) := by
  let s := nndist R.start x
  have at_s : R.radialPoint outward nonzero s = x := by
    apply R.eq_of_radius_eq outward nonzero (R.radialPoint_mem outward nonzero s) member
    rw [dist_eq_norm', R.norm_radialPoint_sub_start]
    rfl
  have radii : |(s : ℝ) - (r : ℝ)| ≤ ‖z - x‖ := by
    change |dist R.start x - (r : ℝ)| ≤ _
    rw [dist_eq_norm', ← radius]
    exact (abs_norm_sub_norm_le _ _).trans_eq (by rw [sub_sub_sub_cancel_right, norm_sub_rev])
  have inverse_error : ‖x - R.radialPoint outward nonzero r‖ ≤ (K : ℝ) * ‖z - x‖ := by
    have bound := inverse.dist_le_mul s r
    rw [at_s, dist_eq_norm, NNReal.dist_eq] at bound
    exact bound.trans (mul_le_mul_of_nonneg_left radii K.coe_nonneg)
  have size : (1 - ε) * ‖x - R.start‖ ≤ (r : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub x z R.start
    rw [norm_sub_rev x z, radius] at triangle
    nlinarith
  have upper : ‖x - R.start‖ ≤ (r : ℝ) / (1 - ε) := by
    apply (le_div_iff₀ (sub_pos.mpr small)).mpr
    nlinarith
  have point_error : ‖z - x‖ ≤ (ε / (1 - ε)) * (r : ℝ) := by
    calc
      _ ≤ ε * ‖x - R.start‖ := error
      _ ≤ ε * ((r : ℝ) / (1 - ε)) := mul_le_mul_of_nonneg_left upper nonnegative
      _ = _ := by ring
  calc
    _ ≤ ‖z - x‖ + ‖x - R.radialPoint outward nonzero r‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 + (K : ℝ)) * ‖z - x‖ := by nlinarith
    _ ≤ (1 + (K : ℝ)) * ((ε / (1 - ε)) * (r : ℝ)) :=
      mul_le_mul_of_nonneg_left point_error (by positivity)
    _ = _ := by ring

end Unfoldings.PolygonalRay
