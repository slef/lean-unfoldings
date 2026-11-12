module

public import Unfoldings.Geometry.RadialTailComponentRays

/-! Every nontip point of a radial component has strictly smaller positive linear height. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p x : E} (T : RadialClipTail S q p)

theorem linear_height_lt_tip_of_mem_ne (height : E →ₗ[ℝ] ℝ)
    (positive : 0 < height (T.tip - q)) (member : x ∈ T.carrier) (different : x ≠ T.tip) :
    height (x - q) < height (T.tip - q) := by
  obtain ⟨a, bounds, position⟩ := T.carrier_eq_image.subset member
  change q + a • (T.tip - q) = x at position
  have not_one : a ≠ 1 := by
    intro one
    apply different
    rw [← position, one, one_smul, add_sub_cancel]
  have before : a < 1 := lt_of_le_of_ne bounds.2 not_one
  rw [← position, add_sub_cancel_left, map_smul]
  simp only [smul_eq_mul]
  nlinarith

end Unfoldings.RadialClipTail
