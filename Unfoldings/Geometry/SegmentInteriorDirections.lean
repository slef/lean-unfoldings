module

public import Unfoldings.Geometry.SegmentInteriorGerm

/-! Exact original direction-line germs for segments in arbitrary real normed spaces. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict interior segment points have exactly their original direction line as local
model. The proof uses the actual endpoint clearance, without a coordinate-plane assumption. -/
theorem eventually_mem_segment_iff_direction_line_normed (a b : E) (different : a ≠ b)
    (t : ℝ) (bounds : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ z in 𝓝 (AffineMap.lineMap a b t), z ∈ segment ℝ a b ↔
      z - AffineMap.lineMap a b t ∈ Set.range (fun s : ℝ => s • (b - a)) := by
  have dpos : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
  let radius := min t (1 - t) * ‖b - a‖
  have positive : 0 < radius := mul_pos (lt_min bounds.1 (sub_pos.mpr bounds.2)) dpos
  filter_upwards [Metric.ball_mem_nhds (AffineMap.lineMap a b t) positive] with z near
  constructor
  · intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨s, _bounds, rfl⟩ := member
    refine ⟨s - t, ?_⟩
    simp only [AffineMap.lineMap_apply_module']
    module
  · rintro ⟨s, equal⟩
    have distance : dist z (AffineMap.lineMap a b t) = |s| * ‖b - a‖ := by
      rw [dist_eq_norm, ← equal, norm_smul, Real.norm_eq_abs]
    have small : |s| < min t (1 - t) := by
      have close := Metric.mem_ball.mp near
      rw [distance] at close
      exact (mul_lt_mul_iff_of_pos_right dpos).mp close
    have sbounds := abs_lt.mp small
    have lower : 0 ≤ t + s := by
      have before := min_le_left t (1 - t)
      linarith [sbounds.1]
    have upper : t + s ≤ 1 := by
      have after := min_le_right t (1 - t)
      linarith [sbounds.2]
    have expression : z = AffineMap.lineMap a b (t + s) := by
      have solve : z = s • (b - a) + AffineMap.lineMap a b t :=
        (eq_sub_iff_add_eq.mp equal).symm
      rw [solve]
      simp only [AffineMap.lineMap_apply_module']
      module
    rw [expression]
    exact lineMap_mem_segment ℝ a b ⟨lower, upper⟩

end Unfoldings
