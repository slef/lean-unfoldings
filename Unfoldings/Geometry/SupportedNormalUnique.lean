module

public import Unfoldings.Geometry.SpatialPlane
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! A rigid plane and the choice of interior side determine its unit supporting normal. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Two unit normals to the same rigid plane agree if one point lies strictly on their
negative sides. This includes planes represented by coplanar subdivision triangles. -/
theorem unit_normal_unique (place : Plane →ᵃⁱ[ℝ] Space) (n m : Space)
    (unit_n : ‖n‖ = 1) (unit_m : ‖m‖ = 1)
    (tangent_n : ∀ x, inner ℝ n (place.linear x) = 0)
    (tangent_m : ∀ x, inner ℝ m (place.linear x) = 0)
    (c : Space) (negative_n : inner ℝ n (c - place 0) < 0)
    (negative_m : inner ℝ m (c - place 0) < 0) : n = m := by
  let functional := innerSL ℝ n
  have nonzero : functional ≠ 0 := by
    intro zero
    have value := congrArg (fun f : Space →L[ℝ] ℝ => f n) zero
    change inner ℝ n n = 0 at value
    rw [real_inner_self_eq_norm_sq, unit_n] at value
    norm_num at value
  have level (x : Plane) : functional (place x) = functional (place 0) := by
    have chord := place.toAffineMap.linear_apply_vsub x 0
    change place.linear (x - 0) = place x - place 0 at chord
    rw [sub_zero] at chord
    have tangent := tangent_n x
    rw [chord, inner_sub_right] at tangent
    exact sub_eq_zero.mp tangent
  have kernel := affineIsometry_linear_range_eq_kernel place functional nonzero
    (functional (place 0)) level
  have annihilates (z : Space) (zero : inner ℝ n z = 0) : inner ℝ m z = 0 := by
    have member : z ∈ functional.toLinearMap.ker := zero
    rw [← kernel] at member
    obtain ⟨x, rfl⟩ := member
    exact tangent_m x
  let scale := inner ℝ m n
  have scalar (z : Space) : inner ℝ m z = scale * inner ℝ n z := by
    have zero : inner ℝ n (z - inner ℝ n z • n) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, unit_n]
      ring
    have orthogonal := annihilates _ zero
    rw [inner_sub_right, real_inner_smul_right] at orthogonal
    dsimp only [scale]
    nlinarith
  have positive : 0 < scale := by
    by_contra not_positive
    have nonnegative := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt not_positive) negative_n.le
    have relation := scalar (c - place 0)
    linarith
  have square := scalar m
  rw [real_inner_self_eq_norm_sq, unit_m] at square
  have symmetric : inner ℝ n m = scale := real_inner_comm _ _
  rw [symmetric] at square
  change (1 : ℝ) ^ 2 = scale * scale at square
  have one : scale = 1 := by nlinarith
  have distance := norm_sub_sq_real m n
  rw [unit_n, unit_m] at distance
  change ‖m - n‖ ^ 2 = 1 ^ 2 - 2 * scale + 1 ^ 2 at distance
  rw [one] at distance
  have zero : ‖m - n‖ = 0 := by nlinarith [norm_nonneg (m - n)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp zero)).symm

end Unfoldings
