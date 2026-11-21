module

public import Unfoldings.FewestNets.MeshStarLengths
public import Unfoldings.Geometry.SphericalAngleChord

/-! Transfer checked chord bounds to spherical arc lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open InnerProductGeometry Real

variable {n : ℕ} {star : MeshStar (n + 1)}

/-- The chord expression bounds the spherical angle. -/
theorem angle_le_chord_arcUpper {x y : Space} (unit_x : ‖x‖ = 1) (unit_y : ‖y‖ = 1)
    (small : angle x y < π) :
    angle x y ≤ ‖y - x‖ / sqrt (1 - ‖y - x‖ ^ 2 / 4) :=
  angle_le_chord_arcUpper_of_unit unit_x unit_y small

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
