module

public import Unfoldings.Geometry.LineTransverse

/-! Directed side changes at actual transverse intersections of affine lines. -/

@[expose] public section

namespace Unfoldings

/-- Signed height along a line changes by its actual determinant times the parameter increment. -/
theorem orient_lineMap_sub (a b p q : Plane) (s t : ℝ) :
    orient a b (AffineMap.lineMap p q s) - orient a b (AffineMap.lineMap p q t) =
      (s - t) * orient 0 (b - a) (q - p) := by
  simp only [AffineMap.lineMap_apply_module', orient, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
  ring

/-- A section approaching a directed bank from its left has negative transverse determinant. -/
theorem line_exit_left_sign {a b p q : Plane} {s t : ℝ} (before : s < t)
    (meets : orient a b (AffineMap.lineMap p q t) = 0)
    (side : 0 ≤ orient a b (AffineMap.lineMap p q s))
    (transverse : orient 0 (b - a) (q - p) ≠ 0) :
    orient 0 (b - a) (q - p) < 0 := by
  have identity := orient_lineMap_sub a b p q s t
  rw [meets, sub_zero] at identity
  have product : 0 ≤ (s - t) * orient 0 (b - a) (q - p) := identity ▸ side
  by_contra nonnegative
  have positive := lt_of_le_of_ne (le_of_not_gt nonnegative) (Ne.symm transverse)
  exact not_lt_of_ge product (mul_neg_of_neg_of_pos (sub_neg.mpr before) positive)

/-- A section leaving a directed bank into its left has positive transverse determinant. -/
theorem line_enter_left_sign {a b p q : Plane} {s t : ℝ} (after : t < s)
    (meets : orient a b (AffineMap.lineMap p q t) = 0)
    (side : 0 ≤ orient a b (AffineMap.lineMap p q s))
    (transverse : orient 0 (b - a) (q - p) ≠ 0) :
    0 < orient 0 (b - a) (q - p) := by
  have identity := orient_lineMap_sub a b p q s t
  rw [meets, sub_zero] at identity
  have product : 0 ≤ (s - t) * orient 0 (b - a) (q - p) := identity ▸ side
  by_contra nonpositive
  have negative := lt_of_le_of_ne (le_of_not_gt nonpositive) transverse
  exact not_lt_of_ge product (mul_neg_of_pos_of_neg (sub_pos.mpr after) negative)

end Unfoldings
