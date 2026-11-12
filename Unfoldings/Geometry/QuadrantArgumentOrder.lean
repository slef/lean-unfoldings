module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Coordinate bounds in a source quadrant give exact angular order, including inner barriers. -/

@[expose] public section

namespace Unfoldings

theorem arg_antitone_re_of_norm_eq {x y : ℂ} (first : 0 < x.im) (last : 0 < y.im)
    (radius : ‖x‖ = ‖y‖) (ordered : x.re ≤ y.re) : y.arg ≤ x.arg := by
  rw [Complex.arg_of_im_pos last, Complex.arg_of_im_pos first, ← radius]
  exact Real.arccos_le_arccos (div_le_div_of_nonneg_right ordered (norm_nonneg x))

theorem arg_monotone_im_of_norm_eq {x y : ℂ} (first : 0 ≤ x.re) (last : 0 ≤ y.re)
    (radius : ‖x‖ = ‖y‖) (ordered : x.im ≤ y.im) : x.arg ≤ y.arg := by
  rw [Complex.arg_of_re_nonneg first, Complex.arg_of_re_nonneg last, ← radius]
  exact Real.arcsin_le_arcsin (div_le_div_of_nonneg_right ordered (norm_nonneg x))

/-- A circle point to the left of an inner first-quadrant barrier has larger
argument than that barrier, even though the two points have different radii. -/
theorem arg_lt_of_re_le_inner_barrier {x m : ℂ} (above : 0 < x.im)
    (horizontal : 0 < m.re) (vertical : 0 < m.im)
    (inside : ‖m‖ < ‖x‖) (ordered : x.re ≤ m.re) : m.arg < x.arg := by
  have mpositive : 0 < ‖m‖ := norm_pos_iff.mpr (fun zero => by simp [zero] at horizontal)
  have ratio : x.re / ‖x‖ < m.re / ‖m‖ :=
    (div_le_div_of_nonneg_right ordered (norm_nonneg x)).trans_lt
      (div_lt_div_of_pos_left horizontal mpositive inside)
  rw [Complex.arg_of_im_pos vertical, Complex.arg_of_im_pos above]
  exact Real.arccos_lt_arccos (abs_le.mp (Complex.abs_re_div_norm_le_one x)).1 ratio
    (abs_le.mp (Complex.abs_re_div_norm_le_one m)).2

/-- The corresponding lower circle point has smaller argument than the
inner barrier. This order can be transported between neighboring frames. -/
theorem arg_lt_of_im_le_inner_barrier {y m : ℂ} (rightward : 0 ≤ y.re)
    (horizontal : 0 ≤ m.re) (vertical : 0 < m.im)
    (inside : ‖m‖ < ‖y‖) (ordered : y.im ≤ m.im) : y.arg < m.arg := by
  have mpositive : 0 < ‖m‖ := norm_pos_iff.mpr (fun zero => by simp [zero] at vertical)
  have ratio : y.im / ‖y‖ < m.im / ‖m‖ :=
    (div_le_div_of_nonneg_right ordered (norm_nonneg y)).trans_lt
      (div_lt_div_of_pos_left vertical mpositive inside)
  rw [Complex.arg_of_re_nonneg rightward, Complex.arg_of_re_nonneg horizontal]
  exact Real.arcsin_lt_arcsin (abs_le.mp (Complex.abs_im_div_norm_le_one y)).1 ratio
    (abs_le.mp (Complex.abs_im_div_norm_le_one m)).2

end Unfoldings
