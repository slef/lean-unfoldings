module

public import Unfoldings.Geometry.LevelCrossings
public import Unfoldings.Geometry.Triangle

/-!
# Actual geometric changes of a signed segment-ray counter

A change between two horizontal ray origins produces an actual point of the
original closed segment, at the requested level and between the two origins.
Conversely, a unique transverse intersection inside that interval changes the
counter by the negative level-indicator jump.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Actual segment point at its chosen horizontal-level parameter. -/
def segmentLevelPoint (a b : Plane) (level : ℝ) : Plane :=
  AffineMap.lineMap a b (levelCrossingParameter (a 1) (b 1) level)

/-- Signed horizontal ray count for one actual directed original segment. -/
def segmentRayCounter (a b : Plane) (cut level : ℝ) : ℝ :=
  if cut < segmentLevelPoint a b level 0 then
    levelIndicator level (b 1) - levelIndicator level (a 1) else 0

/-- A genuine indicator change gives an actual original-segment intersection at the level. -/
theorem segmentLevelPoint_mem_of_change {a b : Plane} {level : ℝ}
    (change : levelIndicator level (b 1) ≠ levelIndicator level (a 1)) :
    segmentLevelPoint a b level ∈ segment ℝ a b ∧ segmentLevelPoint a b level 1 = level := by
  refine ⟨lineMap_mem_segment ℝ _ _ (levelCrossingParameter_bounds change), ?_⟩
  have hit := levelCrossingParameter_hits change
  simp only [segmentLevelPoint, AffineMap.lineMap_apply_module', PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  nlinarith only [hit]

/-- A genuine level change has the sign of the segment's transverse displacement. -/
theorem levelIndicator_jump_eq_sign {a b level : ℝ}
    (change : levelIndicator level b ≠ levelIndicator level a) :
    levelIndicator level b - levelIndicator level a = if 0 < b - a then 1 else -1 := by
  by_cases first : level < a <;> by_cases last : level < b
  · simp only [levelIndicator, ite_eq_left first, ite_eq_left last] at change
    exact (change rfl).elim
  · have negative : ¬ 0 < b - a := by linarith [le_of_not_gt last]
    simp only [levelIndicator, ite_eq_left first, ite_eq_right last, ite_eq_right negative]
    norm_num
  · have positive : 0 < b - a := by linarith [le_of_not_gt first]
    simp only [levelIndicator, ite_eq_right first, ite_eq_left last, ite_eq_left positive]
    norm_num
  · simp only [levelIndicator, ite_eq_right first, ite_eq_right last] at change
    exact (change rfl).elim

/-- A nonhorizontal original segment has only one point at the requested level. -/
theorem segmentLevelPoint_eq_of_mem {a b z : Plane} {level : ℝ}
    (different : b 1 - a 1 ≠ 0) (member : z ∈ segment ℝ a b) (hits : z 1 = level) :
    segmentLevelPoint a b level = z := by
  obtain ⟨t, _bounds, image⟩ := (segment_eq_image_lineMap ℝ a b).le member
  have coordinate := congrArg (fun p : Plane => p 1) image
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul] at coordinate
  rw [hits] at coordinate
  have parameter : t = levelCrossingParameter (a 1) (b 1) level := by
    unfold levelCrossingParameter
    exact (eq_div_iff different).mpr (by linarith)
  rw [segmentLevelPoint, ← parameter]
  exact image

/-- A segment meeting the level, with both endpoints off it, changes the level indicator. -/
theorem levelIndicator_ne_of_segment_meeting {a b z : Plane} {level : ℝ}
    (first_ne : a 1 ≠ level) (last_ne : b 1 ≠ level)
    (member : z ∈ segment ℝ a b) (hits : z 1 = level) :
    levelIndicator level (b 1) ≠ levelIndicator level (a 1) := by
  obtain ⟨t, bounds, image⟩ := (segment_eq_image_lineMap ℝ a b).le member
  have coordinate := congrArg (fun p : Plane => p 1) image
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul] at coordinate
  rw [hits] at coordinate
  have real_image : AffineMap.lineMap (a 1) (b 1) t = level := by
    rw [AffineMap.lineMap_apply_ring]
    nlinarith only [coordinate]
  have interval := lineMap_mem_segment ℝ (a 1) (b 1) bounds
  rw [real_image, segment_eq_Icc'] at interval
  by_cases first : level < a 1 <;> by_cases last : level < b 1
  · exact (not_lt_of_ge interval.1 (lt_min first last)).elim
  · simp only [levelIndicator, ite_eq_left first, ite_eq_right last]
    norm_num
  · simp only [levelIndicator, ite_eq_right first, ite_eq_left last]
    norm_num
  · have first_negative := lt_of_le_of_ne (le_of_not_gt first) first_ne
    have last_negative := lt_of_le_of_ne (le_of_not_gt last) last_ne
    exact (not_lt_of_ge interval.2 (max_lt first_negative last_negative)).elim

/-- Nonzero change of ray count yields an actual crossing between the two ordered ray origins. -/
theorem segmentRayCounter_change_meets {a b : Plane} {first last level : ℝ}
    (ordered : first ≤ last)
    (changes : segmentRayCounter a b last level - segmentRayCounter a b first level ≠ 0) :
    segmentLevelPoint a b level ∈ segment ℝ a b ∧
      segmentLevelPoint a b level 1 = level ∧
      first < segmentLevelPoint a b level 0 ∧ segmentLevelPoint a b level 0 ≤ last := by
  have indicator : levelIndicator level (b 1) ≠ levelIndicator level (a 1) := by
    intro same
    simp only [segmentRayCounter, same, sub_self, ite_self] at changes
    exact changes rfl
  obtain ⟨member, hits⟩ := segmentLevelPoint_mem_of_change indicator
  by_cases left : first < segmentLevelPoint a b level 0
  · by_cases right : last < segmentLevelPoint a b level 0
    · simp only [segmentRayCounter, ite_eq_left left, ite_eq_left right, sub_self,
        ne_eq, not_true_eq_false] at changes
    · exact ⟨member, hits, left, le_of_not_gt right⟩
  · have right : ¬ last < segmentLevelPoint a b level 0 :=
      fun h => left (ordered.trans_lt h)
    simp only [segmentRayCounter, ite_eq_right left, ite_eq_right right,
      sub_self, ne_eq, not_true_eq_false] at changes

/-- No original-segment meeting between the origins means no ray-counter change. -/
theorem segmentRayCounter_change_zero_of_avoids {a b : Plane} {first last level : ℝ}
    (ordered : first ≤ last)
    (avoids : ∀ z ∈ segment ℝ a b, z 1 = level → first < z 0 → z 0 ≤ last → False) :
    segmentRayCounter a b last level - segmentRayCounter a b first level = 0 := by
  by_contra changes
  obtain ⟨member, hits, lower, upper⟩ := segmentRayCounter_change_meets ordered changes
  exact avoids _ member hits lower upper

/-- A genuine level intersection strictly between queries changes the signed count exactly. -/
theorem segmentRayCounter_change_at_crossing {a b : Plane} {first last level : ℝ}
    (lower : first < segmentLevelPoint a b level 0)
    (upper : segmentLevelPoint a b level 0 < last) :
    segmentRayCounter a b last level - segmentRayCounter a b first level =
      -(levelIndicator level (b 1) - levelIndicator level (a 1)) := by
  simp only [segmentRayCounter, ite_eq_left lower, ite_eq_right (not_lt_of_ge upper.le), zero_sub]

end Unfoldings
