module

public import Unfoldings.Geometry.StraightGraph

/-! Two forward subsegments with the same initial affine parameter overlap in their interiors. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem openSubsegments_inter_nonempty (a b : E) {s t u : ℝ}
    (first : s < t) (last : s < u) :
    (openSegment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) ∩
      openSegment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b u)).Nonempty := by
  let v := (s + min t u) / 2
  have after : s < v := by dsimp [v]; linarith [lt_min first last]
  have before_t : v < t := by dsimp [v]; linarith [min_le_left t u]
  have before_u : v < u := by dsimp [v]; linarith [min_le_right t u]
  refine ⟨AffineMap.lineMap a b v, ?_, ?_⟩
  · rw [← image_openSegment ℝ (AffineMap.lineMap a b)]
    exact ⟨v, by rw [openSegment_eq_Ioo first]; exact ⟨after, before_t⟩, rfl⟩
  · rw [← image_openSegment ℝ (AffineMap.lineMap a b)]
    exact ⟨v, by rw [openSegment_eq_Ioo last]; exact ⟨after, before_u⟩, rfl⟩

end Unfoldings
