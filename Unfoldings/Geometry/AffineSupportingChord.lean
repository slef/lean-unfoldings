module

public import Unfoldings.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Tactic.Linarith

/-! A nonnegative affine function vanishing inside a chord vanishes at both endpoints. -/

@[expose] public section

namespace Unfoldings

theorem affine_zero_endpoints_of_openSegment (height : Plane →ᵃ[ℝ] ℝ) {a b p : Plane}
    (first : 0 ≤ height a) (last : 0 ≤ height b) (between : p ∈ openSegment ℝ a b)
    (zero : height p = 0) : height a = 0 ∧ height b = 0 := by
  obtain ⟨t, bounds, expression⟩ := (openSegment_eq_image_lineMap ℝ a b).subset between
  have formula := congrArg height expression
  rw [height.apply_lineMap, AffineMap.lineMap_apply_ring, zero] at formula
  have first_zero : height a = 0 := by
    have other := mul_nonneg bounds.1.le last
    have product : (1 - t) * height a = 0 :=
      le_antisymm (by linarith) (mul_nonneg (sub_pos.mpr bounds.2).le first)
    exact (mul_eq_zero.mp product).resolve_left (sub_pos.mpr bounds.2).ne'
  refine ⟨first_zero, ?_⟩
  rw [first_zero, mul_zero, zero_add] at formula
  exact (mul_eq_zero.mp formula).resolve_left bounds.1.ne'

end Unfoldings
