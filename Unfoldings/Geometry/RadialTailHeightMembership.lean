module

public import Unfoldings.Geometry.RadialTailHeightOrder

/-! A later point on the same positive ray remains on the tail until its tip height. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p x y : E} (T : RadialClipTail S q p)

theorem mem_of_scaled_position_of_linear_height (height : E →ₗ[ℝ] ℝ)
    (positive : 0 < height (T.tip - q)) (member : x ∈ T.carrier)
    {a : ℝ} (scale : y - q = a • (x - q))
    (after : height (x - q) ≤ height (y - q))
    (before : height (y - q) ≤ height (T.tip - q)) : y ∈ T.carrier := by
  obtain ⟨r, bounds, position⟩ := T.carrier_eq_image.subset member
  have vector : x - q = r • (T.tip - q) := by rw [← position, add_sub_cancel_left]
  have at_y : y = q + (a * r) • (T.tip - q) := by
    rw [vector, smul_smul] at scale
    exact (sub_eq_iff_eq_add.mp scale).trans (add_comm _ _)
  have ordered : r ≤ a * r := by
    rw [scale, vector] at after
    simp only [map_smul, smul_eq_mul, ← mul_assoc] at after
    exact (mul_le_mul_iff_left₀ positive).mp after
  have last : a * r ≤ 1 := by
    rw [at_y, add_sub_cancel_left, map_smul] at before
    simpa only [smul_eq_mul, one_mul] using (mul_le_iff_le_one_left positive).mp before
  exact T.carrier_eq_image.symm.subset ⟨a * r, ⟨bounds.1.trans ordered, last⟩, at_y.symm⟩

end Unfoldings.RadialClipTail
