module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Unsigned angles between the rays of a two-generator cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonnegative combination of two rays stays within their angle from the first ray. -/
theorem angle_le_of_nonnegative_combination {u v : E} {a b : ℝ}
    (u_ne : u ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (w_ne : a • u + b • v ≠ 0) :
    angle u (a • u + b • v) ≤ angle u v := by
  let w := a • u + b • v
  let c := Real.cos (angle u v)
  let A := a * ‖u‖
  let B := b * ‖v‖
  have Au : ‖a • u‖ = A := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have Bv : ‖b • v‖ = B := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have upper : ‖w‖ ≤ A + B := by
    change ‖a • u + b • v‖ ≤ A + B
    rw [← Au, ← Bv]
    exact norm_add_le _ _
  have lower : B - A ≤ ‖w‖ := by
    have h := norm_sub_norm_le (b • v) (-(a • u))
    rw [norm_neg, sub_neg_eq_add, add_comm, Au, Bv] at h
    exact h
  have A_nonneg : 0 ≤ A := mul_nonneg ha (norm_nonneg _)
  have comparison : c * ‖w‖ ≤ A + B * c := by
    by_cases hc : 0 ≤ c
    · calc
        _ ≤ c * (A + B) := mul_le_mul_of_nonneg_left upper hc
        _ ≤ _ := by
          have cos_le : c ≤ 1 := Real.cos_le_one _
          linarith only [mul_le_mul_of_nonneg_left cos_le A_nonneg]
    · calc
        _ ≤ c * (B - A) := mul_le_mul_of_nonpos_left lower (le_of_not_ge hc)
        _ ≤ _ := by
          have cos_ge : -1 ≤ c := Real.neg_one_le_cos _
          linarith only [mul_le_mul_of_nonneg_left cos_ge A_nonneg]
  have dot : inner ℝ u w = ‖u‖ * (A + B * c) := by
    change inner ℝ u (a • u + b • v) = _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ← cos_angle_mul_norm_mul_norm]
    dsimp only [A, B, c]
    ring
  change angle u w ≤ angle u v
  apply (Real.strictAntiOn_cos.le_iff_ge
    ⟨angle_nonneg u v, angle_le_pi u v⟩ ⟨angle_nonneg u w, angle_le_pi u w⟩).mp
  change c ≤ Real.cos (angle u w)
  rw [cos_angle, dot, le_div_iff₀ (mul_pos (norm_pos_iff.mpr u_ne) (norm_pos_iff.mpr w_ne))]
  calc
    c * (‖u‖ * ‖w‖) = ‖u‖ * (c * ‖w‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left comparison (norm_nonneg u)

end Unfoldings
