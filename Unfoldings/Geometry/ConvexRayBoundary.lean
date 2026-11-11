module

public import Unfoldings.Geometry.ConvexSegmentExit
public import Unfoldings.Geometry.ConvexRadialTails
public import Mathlib.Tactic.FieldSimp

/-! Genuine radial boundary points of compact convex bodies, from arbitrary interior centers. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every nonzero ray from an interior point meets the actual convex frontier. -/
theorem exists_frontier_on_positive_ray {S : Set E} (compact : IsCompact S) (convex : Convex ℝ S)
    {q x : E} (inside : q ∈ interior S) (different : x ≠ q) :
    ∃ a : ℝ, 0 < a ∧ q + a • (x - q) ∈ frontier S := by
  have translated : IsCompact ((fun p : E => p - q) '' S) :=
    compact.image (continuous_id.sub continuous_const)
  obtain ⟨M, M_pos, bound⟩ := translated.isBounded.exists_pos_norm_le
  have norm_positive : 0 < ‖x - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different)
  let a := (M + 1) / ‖x - q‖
  have a_positive : 0 < a := div_pos (by linarith) norm_positive
  have outside : q + a • (x - q) ∉ S := by
    intro member
    have bounded := bound ((q + a • (x - q)) - q) ⟨_, member, rfl⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos a_positive] at bounded
    dsimp only [a] at bounded
    rw [div_mul_cancel₀ _ norm_positive.ne'] at bounded
    linarith
  obtain ⟨t, bounds, boundary⟩ := exists_frontier_on_segment compact convex inside outside
  refine ⟨t * a, mul_pos bounds.1 a_positive, ?_⟩
  have point : AffineMap.lineMap q (q + a • (x - q)) t = q + (t * a) • (x - q) := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, add_comm]
  rwa [point] at boundary

/-- A frontier point on a ray is at least as far as any supplied point of the body. -/
theorem one_le_frontier_ray_factor {S : Set E} (convex : Convex ℝ S)
    {q x : E} (origin : q ∈ interior S) (member : x ∈ S) {a : ℝ} (positive : 0 < a)
    (boundary : q + a • (x - q) ∈ frontier S) : 1 ≤ a := by
  by_contra less
  have inverse : 1 < a⁻¹ := (one_lt_inv₀ positive).mpr (lt_of_not_ge less)
  have excluded := radial_tail_not_mem_closure convex origin boundary inverse
  have identity : q + a⁻¹ • ((q + a • (x - q)) - q) = x := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ positive.ne', one_smul, add_sub_cancel]
  rw [identity] at excluded
  exact excluded (subset_closure member)

end Unfoldings
