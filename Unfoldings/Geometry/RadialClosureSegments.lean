module

public import Unfoldings.Geometry.RadialGraphArc
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! Exact disk and half-plane separation of the three radial-wedge closing segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scaling any direction with positive terminal scalar product gives a genuine outer corner. -/
theorem exists_outward_closing_point (q b direction : E)
    (outward : 0 < inner ℝ (b - q) direction) :
    ∃ t : ℝ, 0 < t ∧ 0 < inner ℝ (b - q) (q + t • direction - b) := by
  let t := (‖b - q‖ ^ 2 + 1) / inner ℝ (b - q) direction
  have positive : 0 < t := div_pos (by positivity) outward
  refine ⟨t, positive, ?_⟩
  have difference : q + t • direction - b = t • direction - (b - q) := by abel
  rw [difference, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have product : t * inner ℝ (b - q) direction = ‖b - q‖ ^ 2 + 1 :=
    div_mul_cancel₀ _ outward.ne'
  linarith

theorem dist_closing_strict (q b c : E) (outward : 0 < inner ℝ (b - q) (c - b))
    {t : ℝ} (positive : 0 < t) : dist q b < dist q (AffineMap.lineMap b c t) := by
  have different : b ≠ c := by
    intro same
    rw [same, sub_self, inner_zero_right] at outward
    exact lt_irrefl 0 outward
  simpa only [AffineMap.lineMap_apply_zero] using
    dist_lineMap_lt_of_inner_nonneg q b c outward.le different (le_refl (0 : ℝ)) positive

theorem dist_initial_segment_le (q a : E) {x : E} (member : x ∈ segment ℝ q a) :
    dist q x ≤ dist q a := by
  have contained := (convex_closedBall q (dist q a)).segment_subset
    (Metric.mem_closedBall_self dist_nonneg)
    (show a ∈ Metric.closedBall q (dist q a) by
      simp only [Metric.mem_closedBall, dist_comm, le_refl])
  simpa only [Metric.mem_closedBall, dist_comm] using contained member

/-- The initial connector touches its terminal source-centered sphere only at its endpoint. -/
theorem initial_segment_inter_radial_exterior (q a : E) :
    segment ℝ q a ∩ {x | dist q a ≤ dist q x} = {a} := by
  ext x
  constructor
  · rintro ⟨member, lower⟩
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, bounds, rfl⟩ := member
    let u : unitInterval := ⟨t, bounds⟩
    have radial : Monotone (fun s : unitInterval => dist q (AffineMap.lineMap q a (s : ℝ))) :=
      (monotone_dist_lineMap_iff q q a).mpr (by simp)
    have upper := radial (show u ≤ 1 from bounds.2)
    change dist q (AffineMap.lineMap q a t) ≤ dist q (AffineMap.lineMap q a 1) at upper
    rw [AffineMap.lineMap_apply_one] at upper
    have same := lineMap_eq_of_dist_eq q q a radial u 1
      (by simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one] using le_antisymm upper lower)
    simpa only [Set.mem_singleton_iff, u, Set.Icc.coe_one, AffineMap.lineMap_apply_one] using same
  · rintro rfl
    exact ⟨right_mem_segment ℝ _ _, show dist q x ≤ dist q x from le_rfl⟩

/-- The terminal connector leaves the whole terminal disk immediately. -/
theorem terminal_segment_inter_radial_disk (q b c : E)
    (outward : 0 < inner ℝ (b - q) (c - b)) :
    segment ℝ b c ∩ {x | dist q x ≤ dist q b} = {b} := by
  ext x
  constructor
  · rintro ⟨member, upper⟩
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, bounds, rfl⟩ := member
    by_cases zero : t = 0
    · simp [zero]
    · exact False.elim ((not_lt_of_ge upper)
        (dist_closing_strict q b c outward (lt_of_le_of_ne bounds.1 (Ne.symm zero))))
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, show dist q x ≤ dist q x from le_rfl⟩

theorem linear_nonnegative_on_initial_segment (height : E →ₗ[ℝ] ℝ) (q a : E)
    (endpoint : 0 ≤ height (a - q)) {x : E} (member : x ∈ segment ℝ q a) :
    0 ≤ height (x - q) := by
  rw [segment_eq_image_lineMap] at member
  obtain ⟨t, bounds, rfl⟩ := member
  simp only [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul, smul_eq_mul]
  exact mul_nonneg bounds.1 endpoint

/-- A strictly opposite closing ray meets an entire supported connector only at the source. -/
theorem source_segments_inter (height : E →ₗ[ℝ] ℝ) (q a c : E)
    (inside : 0 ≤ height (a - q)) (outside : height (c - q) < 0) :
    segment ℝ q a ∩ segment ℝ q c = {q} := by
  ext x
  constructor
  · rintro ⟨first, last⟩
    have nonnegative := linear_nonnegative_on_initial_segment height q a inside first
    rw [segment_eq_image_lineMap] at last
    obtain ⟨t, bounds, rfl⟩ := last
    have formula : height (AffineMap.lineMap q c t - q) = t * height (c - q) := by
      simp only [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul, smul_eq_mul]
    rw [formula] at nonnegative
    have zero : t = 0 := by nlinarith [bounds.1]
    simp [zero]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- The two closing segments at the outer corner have no additional intersection. -/
theorem source_terminal_segments_inter (height : E →ₗ[ℝ] ℝ) (q b c : E)
    (inside : 0 ≤ height (b - q)) (outside : height (c - q) < 0)
    (outward : 0 < inner ℝ (b - q) (c - b)) :
    segment ℝ q c ∩ segment ℝ b c = {c} := by
  ext x
  constructor
  · rintro ⟨first, last⟩
    rw [segment_eq_image_lineMap] at first last
    obtain ⟨t, tbounds, first⟩ := first
    obtain ⟨s, sbounds, last⟩ := last
    have joined := first.trans last.symm
    rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module'] at joined
    have proportional : (t - s) • (c - q) = (1 - s) • (b - q) := by
      apply sub_eq_zero.mp
      have difference : (t - s) • (c - q) - (1 - s) • (b - q) =
          (t • (c - q) + q) - (s • (c - b) + b) := by module
      rw [difference, joined, sub_self]
    have height_equal := congrArg height proportional
    simp only [map_smul, smul_eq_mul] at height_equal
    have height_product : 0 ≤ (t - s) * height (c - q) := by
      rw [height_equal]
      exact mul_nonneg (sub_nonneg.mpr sbounds.2) inside
    have nonpositive : t - s ≤ 0 := by
      rcases mul_nonneg_iff.mp height_product with bad | good
      · exact False.elim (not_le_of_gt outside bad.2)
      · exact good.1
    have normal_positive : 0 < inner ℝ (b - q) (c - q) := by
      have sum : c - q = (c - b) + (b - q) := by abel
      rw [sum, inner_add_right, real_inner_self_eq_norm_sq]
      linarith [sq_nonneg ‖b - q‖]
    have inner_equal := congrArg (inner ℝ (b - q)) proportional
    simp only [real_inner_smul_right, real_inner_self_eq_norm_sq] at inner_equal
    have inner_product : 0 ≤ (t - s) * inner ℝ (b - q) (c - q) := by
      rw [inner_equal]
      exact mul_nonneg (sub_nonneg.mpr sbounds.2) (sq_nonneg _)
    have nonnegative : 0 ≤ t - s := by
      rcases mul_nonneg_iff.mp inner_product with good | bad
      · exact good.1
      · exact False.elim (not_le_of_gt normal_positive bad.2)
    have equal : t - s = 0 := le_antisymm nonpositive nonnegative
    rw [equal, zero_mul] at inner_equal
    have different : b ≠ q := by
      intro same
      rw [same, sub_self, inner_zero_left] at outward
      exact lt_irrefl 0 outward
    have square_positive : 0 < ‖b - q‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr different))
    have terminal : s = 1 := by nlinarith [sbounds.2]
    have initial : t = 1 := by linarith
    rw [initial, AffineMap.lineMap_apply_one] at first
    exact Set.mem_singleton_iff.mpr first.symm
  · rintro rfl
    exact ⟨right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩

end Unfoldings
