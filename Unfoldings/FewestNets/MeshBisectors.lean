module

public import Unfoldings.FewestNets.MeshStar

/-! The star formulas are the gnomonic bisector equations of its spherical sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

theorem inner_eq_coordinate_dotProduct (a b : Space) :
    inner ℝ a b = dotProduct (WithLp.ofLp a) (WithLp.ofLp b) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

@[simp]
theorem inner_left_spatialCross (a b : Space) : inner ℝ a (spatialCross a b) = 0 := by
  rw [inner_eq_coordinate_dotProduct]
  exact dot_self_cross (WithLp.ofLp a) (WithLp.ofLp b)

@[simp]
theorem inner_right_spatialCross (a b : Space) : inner ℝ b (spatialCross a b) = 0 := by
  rw [inner_eq_coordinate_dotProduct]
  exact dot_cross_self (WithLp.ofLp a) (WithLp.ofLp b)

/-- The tangent component of the other site at the chart center. -/
def bisectorTangent (s t : Space) : Space := t - inner ℝ s t • s

/-- Translate and rescale a normal into the tangent plane of the center. -/
def meshGnomonic (s n : Space) : Space := (inner ℝ s n)⁻¹ • n - s

/-- A nearest-site test becomes an affine halfspace in gnomonic coordinates.
The formula does not require knowing whether the competitor gives a facet. -/
theorem inner_meshGnomonic_bisectorTangent_le_iff {s t n : Space}
    (unit : ‖s‖ = 1) (positive : 0 < inner ℝ s n) :
    inner ℝ (meshGnomonic s n) (bisectorTangent s t) ≤ 1 - inner ℝ s t ↔
      inner ℝ n t ≤ inner ℝ n s := by
  have ss : inner ℝ s s = 1 := by
    rw [real_inner_self_eq_norm_sq, unit]
    norm_num
  have orthogonal : inner ℝ (meshGnomonic s n) s = 0 := by
    rw [meshGnomonic, inner_sub_left, real_inner_smul_left, real_inner_comm s n, ss,
      inv_mul_cancel₀ positive.ne', sub_self]
  rw [bisectorTangent, inner_sub_right, real_inner_smul_right, orthogonal, mul_zero, sub_zero,
    meshGnomonic, inner_sub_left, real_inner_smul_left, sub_le_sub_iff_right, ← div_eq_inv_mul,
    div_le_iff₀ positive, one_mul, real_inner_comm s n]

namespace MeshStar

variable {n : ℕ} (star : MeshStar (n + 1)) (i : Fin (n + 1))

/-- The proposed dual vertex is equidistant in angular order from the central
site and the two neighbors that define the chord triangle. -/
theorem inner_dual_eq_neighbors :
    inner ℝ star.direction (star.dual i) = inner ℝ (star.neighborDirection i) (star.dual i) ∧
      inner ℝ star.direction (star.dual i) =
        inner ℝ (star.neighborDirection (i + 1)) (star.dual i) := by
  have hl : inner ℝ (star.neighborDirection i - star.direction) (star.dual i) = 0 :=
    inner_left_spatialCross _ _
  have hr : inner ℝ (star.neighborDirection (i + 1) - star.direction) (star.dual i) = 0 :=
    inner_right_spatialCross _ _
  rw [inner_sub_left, sub_eq_zero] at hl hr
  exact ⟨hl.symm, hr.symm⟩

/-- Normalizing the dual normal does not change its gnomonic coordinates. -/
theorem gnomonicVertex_eq_meshGnomonic_dualDirection
    (positive : 0 < inner ℝ star.direction (star.dual i)) :
    star.gnomonicVertex i = meshGnomonic star.direction (star.dualDirection i) := by
  have ne : star.dual i ≠ 0 := by
    intro h
    simp [h] at positive
  rw [gnomonicVertex, meshGnomonic, dualDirection, NormedSpace.normalize,
    real_inner_smul_right, smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_inv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ne), mul_one]

end MeshStar
end Unfoldings.FewestNets
