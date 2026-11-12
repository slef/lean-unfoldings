module

public import Unfoldings.Geometry.RadialTailHeightOrder

/-! The seed minimizes every linear coordinate increasing along its radial continuation. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p x : E} (T : RadialClipTail S q p)

theorem linear_height_seed_le_of_mem (height : E →ₗ[ℝ] ℝ)
    (positive : 0 ≤ height (T.tip - q)) (member : x ∈ T.carrier) :
    height (p - q) ≤ height (x - q) := by
  obtain ⟨a, bounds, position⟩ := T.carrier_eq_image.subset member
  rw [T.seed_eq, ← position, add_sub_cancel_left, add_sub_cancel_left, map_smul, map_smul]
  exact mul_le_mul_of_nonneg_right bounds.1 positive

end Unfoldings.RadialClipTail
