module

public import Unfoldings.FewestNets.MeshStarLengths

/-! Transfer checked chord bounds to spherical arc lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open InnerProductGeometry Real

variable {n : ℕ} {star : MeshStar (n + 1)}

/-- The chord expression is twice the tangent of half the side angle. -/
theorem angle_le_chord_arcUpper {x y : Space} (unit_x : ‖x‖ = 1) (unit_y : ‖y‖ = 1)
    (small : angle x y < π) :
    angle x y ≤ ‖y - x‖ / sqrt (1 - ‖y - x‖ ^ 2 / 4) := by
  let t := angle x y / 2
  have nonnegative : 0 ≤ t := div_nonneg (angle_nonneg _ _) (by norm_num)
  have half_lt : t < π / 2 := by dsimp [t]; linarith
  have sin_pos : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos])
  have cos_pos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], half_lt⟩
  have angle_eq : angle x y = 2 * t := by dsimp [t]; ring
  have chord := norm_sub_pow_two_real y x
  rw [unit_x, unit_y, inner_eq_cos_angle_of_norm_eq_one unit_y unit_x, angle_comm y x,
    angle_eq, cos_two_mul] at chord
  have root : sqrt (1 - ‖y - x‖ ^ 2 / 4) = cos t := by
    rw [show 1 - ‖y - x‖ ^ 2 / 4 = cos t ^ 2 by linarith only [chord],
      sqrt_sq cos_pos.le]
  have length : ‖y - x‖ = 2 * sin t :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (by
      nlinarith only [chord, sin_sq_add_cos_sq t])
  rw [root, length, mul_div_assoc, ← tan_eq_sin_div_cos]
  have tan := le_tan nonnegative half_lt
  dsimp [t] at tan
  linarith only [tan]

/-- Consecutive outward normals lie in a common open hemisphere. The checked
chord bound therefore bounds the length of their unique minor arc. -/
theorem dualAngle_le_dualArcUpper (i : Fin (n + 1))
    (positive : ∀ j, 0 < inner ℝ star.direction (star.dual j)) :
    angle (star.dualDirection i) (star.dualDirection (i + 1)) ≤ star.dualArcUpper i := by
  have ne (j : Fin (n + 1)) : star.dual j ≠ 0 := by
    intro zero
    simpa [zero] using positive j
  have unit (j : Fin (n + 1)) : ‖star.dualDirection j‖ = 1 :=
    NormedSpace.norm_normalize (ne j)
  have hemisphere (j : Fin (n + 1)) : 0 < inner ℝ star.direction (star.dualDirection j) := by
    rw [dualDirection, NormedSpace.normalize, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (ne j))) (positive j)
  have small : angle (star.dualDirection i) (star.dualDirection (i + 1)) < π := by
    apply lt_of_le_of_ne (angle_le_pi _ _)
    intro eq
    obtain ⟨_, r, negative, opposite⟩ := angle_eq_pi_iff.mp eq
    have h := hemisphere (i + 1)
    rw [opposite, real_inner_smul_right] at h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg negative.le (hemisphere i).le)) h
  exact angle_le_chord_arcUpper (unit i) (unit (i + 1)) small

end Unfoldings.FewestNets.MeshStar
