module

public import Unfoldings.Cap.VerticalProduct
public import Mathlib.Analysis.Convex.Basic

/-! A positive equatorial disk and both poles force an interior origin. -/

@[expose] public section

namespace Unfoldings

/-- An equatorial disk and the two unit poles give a three-dimensional
neighborhood of the origin in any convex set containing them. -/
theorem zero_mem_interior_of_equatorial_disk {S : Set Space} (convex : Convex ℝ S)
    {r : ℝ} (positive : 0 < r)
    (equator : ∀ p : Plane, ‖p‖ < r → Cap.horizontalAtHeight p 0 ∈ S)
    (north : Cap.horizontalAtHeight 0 1 ∈ S) (south : Cap.horizontalAtHeight 0 (-1) ∈ S) :
    (0 : Space) ∈ interior S := by
  apply mem_interior_iff_mem_nhds.mpr
  refine Metric.mem_nhds_iff.mpr ⟨min (r / 2) (1 / 2), lt_min (half_pos positive) (by norm_num), ?_⟩
  intro z hz
  have radial : ‖z‖ < min (r / 2) (1 / 2) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have flat : ‖Cap.horizontal z‖ < r / 2 :=
    (Cap.horizontal_norm_le z).trans_lt (radial.trans_le (min_le_left _ _))
  have vertical : |z 2| ≤ ‖z‖ := by
    have squares := Cap.horizontal_norm_sq z
    apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs]
    linarith only [squares, sq_nonneg ‖Cap.horizontal z‖]
  let t := |z 2|
  have t_nonneg : 0 ≤ t := abs_nonneg _
  have t_small : t < 1 / 2 := vertical.trans_lt (radial.trans_le (min_le_right _ _))
  have a_pos : 0 < 1 - t := by linarith only [t_small]
  let p := (1 - t)⁻¹ • Cap.horizontal z
  have p_small : ‖p‖ < r := by
    rw [show ‖p‖ = ‖Cap.horizontal z‖ / (1 - t) by
      dsimp only [p]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr a_pos), div_eq_inv_mul]]
    apply (div_lt_iff₀ a_pos).mpr
    exact flat.trans_le (by nlinarith only [t_small, mul_le_mul_of_nonneg_left t_small.le positive.le])
  let b := if 0 ≤ z 2 then (1 : ℝ) else -1
  have pole : Cap.horizontalAtHeight 0 b ∈ S := by
    dsimp only [b]
    split
    · exact north
    · exact south
  have height : t * b = z 2 := by
    dsimp only [b, t]
    split
    · rw [abs_of_nonneg (by assumption), mul_one]
    · rw [abs_of_neg (lt_of_not_ge (by assumption))]
      ring
  have plane : (1 - t) • p = Cap.horizontal z := by
    dsimp only [p]
    rw [smul_smul, mul_inv_cancel₀ a_pos.ne', one_smul]
  have z_eq : (1 - t) • Cap.horizontalAtHeight p 0 + t • Cap.horizontalAtHeight 0 b = z := by
    ext i
    fin_cases i
    · have point := congrArg (fun q : Plane => q 0) plane
      simpa [Cap.horizontalAtHeight, Cap.horizontal, PiLp.add_apply, PiLp.smul_apply] using point
    · have point := congrArg (fun q : Plane => q 1) plane
      simpa [Cap.horizontalAtHeight, Cap.horizontal, PiLp.add_apply, PiLp.smul_apply] using point
    · simpa [Cap.horizontalAtHeight, PiLp.add_apply, PiLp.smul_apply] using height
  exact z_eq ▸ convex (equator p p_small) pole a_pos.le t_nonneg (sub_add_cancel _ _)

end Unfoldings
