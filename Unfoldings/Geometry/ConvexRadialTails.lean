module

public import Unfoldings.Geometry.ConvexBoundaryRays
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Radial tails beyond a convex frontier stay outside and have distinct endpoint labels. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q r p : E}

/-- Extending an interior-to-boundary ray beyond the boundary leaves even the closure. -/
theorem radial_tail_not_mem_closure (convex : Convex ℝ S) (origin : q ∈ interior S)
    (boundary : r ∈ frontier S) {a : ℝ} (beyond : 1 < a) :
    q + a • (r - q) ∉ closure S := by
  intro member
  have positive : 0 < a := lt_trans zero_lt_one beyond
  have inverse_small : a⁻¹ < 1 := (inv_lt_one₀ positive).mpr beyond
  have interior_point := convex.combo_interior_closure_mem_interior origin member
    (sub_pos.mpr inverse_small) (inv_nonneg.mpr positive.le)
    (show (1 - a⁻¹) + a⁻¹ = 1 by ring)
  have identity : (1 - a⁻¹) • q + a⁻¹ • (q + a • (r - q)) = r := by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ positive.ne', one_smul,
      sub_smul, smul_sub]
    abel
  rw [identity] at interior_point
  exact boundary.2 interior_point

/-- Two positive rays from an interior point cannot meet at different frontier labels. -/
theorem frontier_eq_of_radial_rays_meet (convex : Convex ℝ S) (origin : q ∈ interior S)
    (first : r ∈ frontier S) (last : p ∈ frontier S)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (same : q + a • (r - q) = q + b • (p - q)) : r = p := by
  have vectors : a • (r - q) = b • (p - q) := add_left_cancel same
  have ratio : r = q + (b / a) • (p - q) := by
    have divided := congrArg (fun v : E => a⁻¹ • v) vectors
    simp only [smul_smul, inv_mul_cancel₀ a_pos.ne', one_smul] at divided
    rw [div_eq_mul_inv, mul_comm b]
    rw [← divided]
    abel
  rcases lt_trichotomy a b with less | equal | greater
  · have beyond : 1 < b / a := (one_lt_div a_pos).mpr less
    exact (radial_tail_not_mem_closure convex origin last beyond (ratio ▸ first.1)).elim
  · rw [equal, div_self b_pos.ne', one_smul] at ratio
    simpa only [add_sub_cancel] using ratio
  · have reverse : p = q + (a / b) • (r - q) := by
      have divided := congrArg (fun v : E => b⁻¹ • v) vectors.symm
      simp only [smul_smul, inv_mul_cancel₀ b_pos.ne', one_smul] at divided
      rw [div_eq_mul_inv, mul_comm a]
      rw [← divided]
      abel
    have beyond : 1 < a / b := (one_lt_div b_pos).mpr greater
    exact (radial_tail_not_mem_closure convex origin first beyond (reverse ▸ last.1)).elim

end Unfoldings
