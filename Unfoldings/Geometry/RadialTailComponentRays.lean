module

public import Unfoldings.Geometry.RadialTailPositions
public import Unfoldings.Geometry.RadialTailFamily

/-! Positive source rays determine unique clipped radial components. -/

@[expose] public section

namespace Unfoldings

namespace RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p r x y : E} (T : RadialClipTail S q p) (U : RadialClipTail S q r)

/-- The convex outer rim meets this whole radial component only at its tip. -/
theorem eq_tip_of_mem_frontier (convex : Convex ℝ S) (origin : q ∈ interior S)
    (member : x ∈ T.carrier) (boundary : x ∈ frontier S) : x = T.tip := by
  obtain ⟨a, positive, at_tip⟩ := T.exists_tip_scale_of_mem member
  exact frontier_eq_of_radial_rays_meet convex origin boundary T.boundary positive zero_lt_one
    (by simpa only [one_smul, add_sub_cancel] using at_tip)

/-- Any linear coordinate increasing along the ray distinguishes all its
physical positions, even when the two positions belong to different fine edges. -/
theorem eq_of_mem_of_linear_height (height : E →ₗ[ℝ] ℝ)
    (positive : 0 < height (T.tip - q))
    (first : x ∈ T.carrier) (last : y ∈ T.carrier) (same : height x = height y) : x = y := by
  obtain ⟨a, _, at_first⟩ := T.carrier_eq_image.subset first
  obtain ⟨b, _, at_last⟩ := T.carrier_eq_image.subset last
  rw [← at_first, ← at_last, map_add, map_add, map_smul, map_smul] at same
  simp only [smul_eq_mul] at same
  have equal : a = b := mul_right_cancel₀ positive.ne' (add_left_cancel same)
  rw [← at_first, ← at_last, equal]

theorem tip_eq_of_pos_scaled_positions (convex : Convex ℝ S) (origin : q ∈ interior S)
    (first : x ∈ T.carrier) (last : y ∈ U.carrier)
    {a : ℝ} (positive : 0 < a) (scale : y - q = a • (x - q)) : T.tip = U.tip := by
  obtain ⟨b, bpos, first_scale⟩ := T.exists_tip_scale_of_mem first
  obtain ⟨c, cpos, last_scale⟩ := U.exists_tip_scale_of_mem last
  have first_vector : T.tip - q = b • (x - q) := by
    rw [← first_scale, add_sub_cancel_left]
  have last_vector : U.tip - q = c • (y - q) := by
    rw [← last_scale, add_sub_cancel_left]
  apply frontier_eq_of_radial_rays_meet convex origin T.boundary U.boundary
    (mul_pos cpos positive) bpos
  rw [first_vector, last_vector, scale, smul_smul, smul_smul, smul_smul]
  congr 1
  congr 1
  ring

end RadialClipTail

namespace RadialTailFamily

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  {S : Set E} {q : E} {seed : I → E} (tail : ∀ i, RadialClipTail S q (seed i))

theorem component_eq_of_pos_scaled_positions (convex : Convex ℝ S) (origin : q ∈ interior S)
    {c d : Component tail} {x y : E}
    (first : x ∈ (componentTail tail c).carrier) (last : y ∈ (componentTail tail d).carrier)
    {a : ℝ} (positive : 0 < a) (scale : y - q = a • (x - q)) : c = d := by
  apply Subtype.ext
  exact (component_tip tail c).symm.trans
    (((componentTail tail c).tip_eq_of_pos_scaled_positions (componentTail tail d)
      convex origin first last positive scale).trans (component_tip tail d))

end RadialTailFamily
end Unfoldings
