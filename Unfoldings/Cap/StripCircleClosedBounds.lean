module

public import Unfoldings.Cap.StripCirclePointBounds
public import Unfoldings.Cap.StripCircleBanks

/-! Closed strip-circle points retain their actual endpoint alternatives and weak bounds. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip.BankCircleSlice

variable {S : MonotoneStrip} {G : ℂ → ℂ} {center : ℂ} {cutoff radius : ℝ}
  (slice : S.BankCircleSlice G center cutoff radius)

theorem closed_circle_image_cases (continuous : Continuous G)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius)
    (interval : S.HasBankCircleInterval G center cutoff radius) {y : ℂ}
    (member : y ∈ G '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - center‖ = radius}) :
    y ∈ G '' S.openSlab 0 cutoff ∩ {z | ‖z - center‖ = radius} ∨
      y = G (S.lower.point slice.lowerHeight) ∨ y = G (S.upper.point slice.upperHeight) := by
  by_cases inside : y ∈ G '' S.openSlab 0 cutoff
  · exact Or.inl ⟨inside, member.2⟩
  · have near : y ∈ closure (G '' S.openSlab 0 cutoff) :=
      image_closure_subset_closure_image continuous member.1
    have boundary : y ∈ frontier (G '' S.openSlab 0 cutoff) :=
      ⟨near, fun interior_point => inside (interior_subset interior_point)⟩
    obtain ⟨lower, upper, at_lower, at_upper, _shape⟩ := interval
    have lower_value := at_lower slice.lowerHeight slice.lower_bounds
      slice.lower_closed slice.lower_radius
    have upper_value := at_upper slice.upperHeight slice.upper_bounds
      slice.upper_closed slice.upper_radius
    rcases S.frontier_circle_bank_points continuous center cutoff radius injective ends_avoid
        boundary member.2 with first | last
    · obtain ⟨h, bounds, closed, size, value⟩ := first
      exact Or.inr (Or.inl
        (value.symm.trans ((at_lower h bounds closed size).trans lower_value.symm)))
    · obtain ⟨h, bounds, closed, size, value⟩ := last
      exact Or.inr (Or.inr
        (value.symm.trans ((at_upper h bounds closed size).trans upper_value.symm)))

theorem closed_circle_image_weak_bounds (continuous : Continuous G)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}))
    (ends_avoid : ∀ z ∈ closure
      {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff},
      (z.re + z.im = 0 ∨ z.re + z.im = cutoff) → ‖G z - center‖ ≠ radius)
    (interval : S.HasBankCircleInterval G center cutoff radius)
    (ordered : (G (S.lower.point slice.lowerHeight) - center).re <
      (G (S.upper.point slice.upperHeight) - center).re)
    (lower_quadrant : 0 ≤ (G (S.lower.point slice.lowerHeight) - center).re ∧
      0 ≤ (G (S.lower.point slice.lowerHeight) - center).im)
    (upper_quadrant : 0 ≤ (G (S.upper.point slice.upperHeight) - center).re ∧
      0 ≤ (G (S.upper.point slice.upperHeight) - center).im)
    {y : ℂ} (quadrant : 0 ≤ (y - center).re ∧ 0 ≤ (y - center).im)
    (member : y ∈ G '' closure (S.openSlab 0 cutoff) ∩ {z | ‖z - center‖ = radius}) :
    (G (S.lower.point slice.lowerHeight) - center).re ≤ (y - center).re ∧
      (y - center).re ≤ (G (S.upper.point slice.upperHeight) - center).re ∧
      (y - center).im ≤ (G (S.lower.point slice.lowerHeight) - center).im := by
  have vertical : (G (S.upper.point slice.upperHeight) - center).im ≤
      (G (S.lower.point slice.lowerHeight) - center).im := by
    have same := congrArg (fun r : ℝ => r ^ 2) (slice.lower_radius.trans slice.upper_radius.symm)
    have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [identity, identity] at same
    exact (quadrant_circle_order lower_quadrant.1 lower_quadrant.2
      upper_quadrant.1 upper_quadrant.2 same (Or.inl ordered.le)).2
  rcases slice.closed_circle_image_cases continuous injective ends_avoid interval member with
    inside | first | last
  · have horizontal := slice.re_bounds_of_mem_circle_image ordered quadrant inside
    exact ⟨horizontal.1.le, horizontal.2.le,
      (slice.im_lt_lower_of_mem_circle_image ordered lower_quadrant quadrant inside).le⟩
  · rw [first]
    exact ⟨le_rfl, ordered.le, le_rfl⟩
  · rw [last]
    exact ⟨ordered.le, le_rfl, vertical⟩

end Unfoldings.MonotoneStrip.BankCircleSlice
