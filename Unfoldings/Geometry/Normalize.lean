module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Radial normalization contracts distances outside the unit ball. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact separation into radial and angular contributions. -/
theorem norm_sub_sq_radial (x y : E) (nonzero_x : x ≠ 0) (nonzero_y : y ≠ 0) :
    ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2 +
      ‖x‖ * ‖y‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ^ 2 := by
  have inner_eq : inner ℝ x y =
      ‖x‖ * ‖y‖ * inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y) := by
    calc
      inner ℝ x y = inner ℝ (‖x‖ • NormedSpace.normalize x)
          (‖y‖ • NormedSpace.normalize y) := by
        rw [NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]
      _ = _ := by rw [real_inner_smul_left, real_inner_smul_right]; ring
  have expand : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 -
      2 * (‖x‖ * ‖y‖ * inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y)) +
      ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_eq]
  rw [expand, norm_sub_sq_real, NormedSpace.norm_normalize nonzero_x,
    NormedSpace.norm_normalize nonzero_y]
  ring

/-- On vectors of norm at least one, normalization is nonexpansive. -/
theorem dist_normalize_le {x y : E} (large_x : 1 ≤ ‖x‖) (large_y : 1 ≤ ‖y‖) :
    dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ dist x y := by
  have nonzero_x : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have nonzero_y : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have identity := norm_sub_sq_radial x y nonzero_x nonzero_y
  have product : 1 ≤ ‖x‖ * ‖y‖ := one_le_mul_of_one_le_of_one_le large_x large_y
  have comparison := mul_le_mul_of_nonneg_right product
    (sq_nonneg ‖NormedSpace.normalize x - NormedSpace.normalize y‖)
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y),
    norm_nonneg (NormedSpace.normalize x - NormedSpace.normalize y)]

end Unfoldings
