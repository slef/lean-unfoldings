module

public import Unfoldings.Geometry.PositiveDirectionFrame
public import Unfoldings.Geometry.RayCounterChanges

/-!
# Geometric ray-counter changes along one actual section line

A nonzero counter difference between ordered section samples gives an actual
original-segment intersection at a section parameter between them. The frame is
positively oriented and sends increasing section parameters to increasing
horizontal coordinates.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A translated linear frame commutes with actual affine interpolation. -/
theorem frame_lineMap_sub (F : Plane ≃ₗᵢ[ℝ] Plane) (p a b : Plane) (t : ℝ) :
    F (AffineMap.lineMap a b t - p) = AffineMap.lineMap (F (a - p)) (F (b - p)) t := by
  simp only [AffineMap.lineMap_apply_module', map_sub, map_add, map_smul]
  module

theorem positiveDirectionFrame_lineMap_horizontal (p q : Plane) (t : ℝ) :
    positiveDirectionFrame (q - p) (AffineMap.lineMap p q t - p) 0 = t * ‖q - p‖ := by
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change t * positiveDirectionFrame (q - p) (q - p) 0 = _
  rw [positiveDirectionFrame_horizontal]

theorem positiveDirectionFrame_lineMap_vertical (p q : Plane) (t : ℝ) :
    positiveDirectionFrame (q - p) (AffineMap.lineMap p q t - p) 1 = 0 := by
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  change t * positiveDirectionFrame (q - p) (q - p) 1 = 0
  rw [positiveDirectionFrame_vertical, mul_zero]

/-- Signed ray count of an actual physical segment from a specified section parameter. -/
def sectionRayCounter (p q a b : Plane) (parameter : ℝ) : ℝ :=
  segmentRayCounter (positiveDirectionFrame (q - p) (a - p))
    (positiveDirectionFrame (q - p) (b - p)) (parameter * ‖q - p‖) 0

/-- Nonzero change supplies a real original-segment intersection between the section queries. -/
theorem sectionRayCounter_change_meets {p q a b : Plane} (different : p ≠ q)
    {first last : ℝ} (ordered : first ≤ last)
    (changes : sectionRayCounter p q a b last - sectionRayCounter p q a b first ≠ 0) :
    ∃ t : ℝ, first < t ∧ t ≤ last ∧ AffineMap.lineMap p q t ∈ segment ℝ a b := by
  let F := positiveDirectionFrame (q - p)
  have length_positive : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
  have ordered_frame := mul_le_mul_of_nonneg_right ordered length_positive.le
  obtain ⟨member, hits, lower, upper⟩ := segmentRayCounter_change_meets ordered_frame changes
  obtain ⟨s, bounds, image⟩ := (segment_eq_image_lineMap ℝ (F (a - p)) (F (b - p))).le member
  let z := AffineMap.lineMap a b s
  have framed : F (z - p) = segmentLevelPoint (F (a - p)) (F (b - p)) 0 := by
    rw [frame_lineMap_sub]
    exact image
  have zero : positiveDirectionFrame (q - p) (z - p) 1 = 0 := by
    rw [framed]
    exact hits
  obtain ⟨r, original⟩ := exists_lineMap_of_positiveFrame_vertical_zero different zero
  have horizontal := congrArg (fun w : Plane => w 0) framed
  rw [original, positiveDirectionFrame_lineMap_horizontal] at horizontal
  rw [← horizontal] at lower upper
  exact ⟨r, (mul_lt_mul_iff_of_pos_right length_positive).mp lower,
    (mul_le_mul_iff_of_pos_right length_positive).mp upper,
    original ▸ lineMap_mem_segment ℝ a b bounds⟩

/-- If no physical segment meets the section interval, its signed ray count stays constant. -/
theorem sectionRayCounter_change_zero_of_avoids {p q a b : Plane} (different : p ≠ q)
    {first last : ℝ} (ordered : first ≤ last)
    (avoids : ∀ t : ℝ, first < t → t ≤ last → AffineMap.lineMap p q t ∉ segment ℝ a b) :
    sectionRayCounter p q a b last - sectionRayCounter p q a b first = 0 := by
  by_contra changes
  obtain ⟨t, lower, upper, member⟩ := sectionRayCounter_change_meets different ordered changes
  exact avoids t lower upper member

/-- A genuine original-segment crossing changes the count with its actual oriented determinant. -/
theorem sectionRayCounter_change_at_crossing {p q a b : Plane} (different : p ≠ q)
    (first_off : positiveDirectionFrame (q - p) (a - p) 1 ≠ 0)
    (last_off : positiveDirectionFrame (q - p) (b - p) 1 ≠ 0)
    {first last r : ℝ} (lower : first < r) (upper : r < last)
    (member : AffineMap.lineMap p q r ∈ segment ℝ a b) :
    sectionRayCounter p q a b last - sectionRayCounter p q a b first =
      if 0 < orient 0 (b - a) (q - p) then 1 else -1 := by
  let F := positiveDirectionFrame (q - p)
  let x := F (a - p)
  let y := F (b - p)
  let z := F (AffineMap.lineMap p q r - p)
  have framed_member : z ∈ segment ℝ x y := by
    obtain ⟨t, bounds, image⟩ := (segment_eq_image_lineMap ℝ a b).le member
    change F (AffineMap.lineMap p q r - p) ∈ segment ℝ (F (a - p)) (F (b - p))
    rw [← image, frame_lineMap_sub]
    exact lineMap_mem_segment ℝ _ _ bounds
  have hits : z 1 = 0 := positiveDirectionFrame_lineMap_vertical p q r
  have indicator : levelIndicator 0 (y 1) ≠ levelIndicator 0 (x 1) :=
    levelIndicator_ne_of_segment_meeting first_off last_off framed_member hits
  have dy_ne : y 1 - x 1 ≠ 0 := by
    intro equal
    exact indicator (congrArg (levelIndicator 0) (sub_eq_zero.mp equal))
  have point_eq : segmentLevelPoint x y 0 = z :=
    segmentLevelPoint_eq_of_mem dy_ne framed_member hits
  have horizontal : z 0 = r * ‖q - p‖ := positiveDirectionFrame_lineMap_horizontal p q r
  have length_positive : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
  have first_bound : first * ‖q - p‖ < segmentLevelPoint x y 0 0 := by
    rw [point_eq, horizontal]
    exact mul_lt_mul_of_pos_right lower length_positive
  have last_bound : segmentLevelPoint x y 0 0 < last * ‖q - p‖ := by
    rw [point_eq, horizontal]
    exact mul_lt_mul_of_pos_right upper length_positive
  have change := segmentRayCounter_change_at_crossing first_bound last_bound
  have displacement : y 1 - x 1 = F (b - a) 1 := by
    have linear := F.map_sub (b - p) (a - p)
    have cancel : (b - p) - (a - p) = b - a := by abel
    rw [cancel] at linear
    exact (congrArg (fun w : Plane => w 1) linear).symm
  have sign : -(if 0 < y 1 - x 1 then (1 : ℝ) else -1) =
      if 0 < orient 0 (b - a) (q - p) then 1 else -1 := by
    have frame_sign := positiveDirectionFrame_transverse_sign
      (sub_ne_zero.mpr different.symm) (edge := b - a)
    by_cases positive : 0 < orient 0 (b - a) (q - p)
    · have negative : y 1 - x 1 < 0 := by rw [displacement]; exact frame_sign.mp positive
      simp only [ite_eq_right (not_lt_of_ge negative.le), ite_eq_left positive, neg_neg]
    · have nonnegative : 0 ≤ y 1 - x 1 := by
        rw [displacement]
        exact le_of_not_gt (fun h => positive (frame_sign.mpr h))
      have above : 0 < y 1 - x 1 := lt_of_le_of_ne nonnegative dy_ne.symm
      simp only [ite_eq_left above, ite_eq_right positive]
  rw [levelIndicator_jump_eq_sign indicator, sign] at change
  exact change

end Unfoldings
