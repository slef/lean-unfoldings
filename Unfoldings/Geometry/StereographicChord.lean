module

public import Unfoldings.Geometry.StereographicConvex

/-! Exact chord distortion in the centered stereographic chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- Squared spatial chord length in the paper's stereographic coordinates. -/
theorem inverseStereographic_chord_sq (x y : Plane) :
    ‖inverseStereographic x - inverseStereographic y‖ ^ 2 =
      4 * ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
  rw [norm_sub_pow_two_real, inverseStereographic_unit, inverseStereographic_unit,
    inverseStereographic_inner, horizontal_inverseStereographic, real_inner_smul_left,
    inverseStereographic_height, norm_sub_pow_two_real]
  field_simp [show 1 + ‖x‖ ^ 2 ≠ 0 by positivity, show 1 + ‖y‖ ^ 2 ≠ 0 by positivity]
  ring

/-- Inverse stereographic projection expands Euclidean chord lengths by at most two. -/
theorem dist_inverseStereographic_le (x y : Plane) :
    dist (inverseStereographic x) (inverseStereographic y) ≤ 2 * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [inverseStereographic_chord_sq]
  have den : 1 ≤ (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by
    nlinarith only [sq_nonneg ‖x‖, sq_nonneg ‖y‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]
  calc
    _ ≤ 4 * ‖x - y‖ ^ 2 := div_le_self (by positivity) den
    _ = _ := by ring

/-- On the closed unit disk the inverse chart expands every chord by at least one. -/
theorem le_dist_inverseStereographic {x y : Plane} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    dist x y ≤ dist (inverseStereographic x) (inverseStereographic y) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [inverseStereographic_chord_sq]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))).2
  calc
    _ ≤ ‖x - y‖ ^ 2 * (2 * 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hx' := (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hx
      have hy' := (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hy
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    _ = _ := by ring

end Unfoldings.Cap
