module

public import Unfoldings.Geometry.LocalRadialPieces

/-! Arbitrarily near radial progress at a segment endpoint characterizes its outward direction. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unlike endpoint distance comparison, local progress rules out an initial inward excursion. -/
theorem localRadialGrowth_segment_start_iff (q a b : E) :
    LocalRadialGrowth (segment ℝ a b) q a ↔
      a ≠ b ∧ 0 ≤ inner ℝ (a - q) (b - a) := by
  constructor
  · intro growth
    have different : a ≠ b := by
      intro equal
      obtain ⟨x, member, _close, farther⟩ := growth 1 zero_lt_one
      have singleton : segment ℝ a b = {a} := by
        simpa only [equal] using segment_same ℝ a
      have at_a : x = a := Set.mem_singleton_iff.mp (singleton.subset member)
      exact (lt_irrefl _ (at_a ▸ farther))
    refine ⟨different, ?_⟩
    by_contra not_outward
    have negative : inner ℝ (a - q) (b - a) < 0 := lt_of_not_ge not_outward
    let h := inner ℝ (a - q) (b - a)
    let k := ‖b - a‖ ^ 2
    let ε := (-h) * ‖b - a‖ / (k + 1)
    have length_pos : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different.symm)
    have k_nonneg : 0 ≤ k := sq_nonneg _
    have denominator : 0 < k + 1 := by linarith
    have h_negative : h < 0 := negative
    have positive : 0 < ε := div_pos (mul_pos (neg_pos.mpr h_negative) length_pos) denominator
    obtain ⟨x, member, close, farther⟩ := growth ε positive
    obtain ⟨s, bounds, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset member
    have near : s * ‖b - a‖ < ε := by
      have length : dist (AffineMap.lineMap a b s) a = s * ‖b - a‖ := by
        simp only [dist_eq_norm, AffineMap.lineMap_apply_module', add_sub_cancel_right,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg bounds.1]
      exact length ▸ (at_x.symm ▸ close)
    have product : s * (k + 1) < -h := by
      apply (mul_lt_mul_iff_left₀ length_pos).mp
      calc
        (s * (k + 1)) * ‖b - a‖ = (s * ‖b - a‖) * (k + 1) := by ring
        _ < ε * (k + 1) := mul_lt_mul_of_pos_right near denominator
        _ = -h * ‖b - a‖ := by
          dsimp [ε]
          rw [div_mul_cancel₀ _ (ne_of_gt denominator)]
    have negative_factor : 2 * h + s * k < 0 := by nlinarith [bounds.1]
    have nonpositive : s * (2 * h + s * k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos bounds.1 negative_factor.le
    have formula := dist_lineMap_sq q a b s
    have square_lt : dist q a ^ 2 < dist q x ^ 2 :=
      (sq_lt_sq₀ dist_nonneg dist_nonneg).mpr farther
    rw [at_x] at formula
    change s * (2 * inner ℝ (a - q) (b - a) + s * ‖b - a‖ ^ 2) ≤ 0 at nonpositive
    nlinarith
  · rintro ⟨different, outward⟩
    exact localRadialGrowth_of_segment_strict
      (fun nonnegative ordered => dist_lineMap_lt_of_inner_nonneg q a b outward different
        nonnegative ordered) (left_mem_segment ℝ a b) different

end Unfoldings
