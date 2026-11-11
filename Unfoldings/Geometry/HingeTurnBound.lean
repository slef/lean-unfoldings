module

public import Unfoldings.Geometry.PlanarAngleAddition

/-!
# Opening a hinge cannot increase a transverse section turn

On one planar halfplane, angular distance is the difference of the two angles
from its boundary ray. Their corresponding spatial angles satisfy the reverse
triangle inequality. This estimate uses local side and angle data only.
-/

@[expose] public section

namespace Unfoldings

/-- In the same strict planar halfplane, two angles from the boundary ray subtract exactly. -/
theorem angle_eq_abs_sub_of_same_halfplane {r x y : Plane}
    (first : 0 < orient 0 r x) (last : 0 < orient 0 r y) :
    InnerProductGeometry.angle x y =
      |InnerProductGeometry.angle r x - InnerProductGeometry.angle r y| := by
  have rne : r ≠ 0 := by intro zero; simp [zero, orient] at first
  have xne : x ≠ 0 := by intro zero; simp [zero, orient] at first
  have yne : y ≠ 0 := by intro zero; simp [zero, orient] at last
  rcases lt_trichotomy (orient 0 x y) 0 with negative | zero | positive
  · have reverse : orient 0 y x = -orient 0 x y := by unfold orient; ring
    have sum := angle_add_of_orient_nonneg rne yne last.le first.le
      (by rw [reverse]; exact neg_pos.mpr negative)
    rw [InnerProductGeometry.angle_comm y x] at sum
    have difference : InnerProductGeometry.angle r x - InnerProductGeometry.angle r y =
        InnerProductGeometry.angle x y := by linarith
    rw [difference, abs_of_nonneg (InnerProductGeometry.angle_nonneg x y)]
  · obtain ⟨t, expression⟩ := exists_lineMap_of_orient_eq_zero xne.symm zero
    rw [AffineMap.lineMap_apply_module'] at expression
    simp only [sub_zero, add_zero] at expression
    have scaled : orient 0 r y = t * orient 0 r x := by
      rw [expression]
      simp only [orient, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
      ring
    have product : 0 < t * orient 0 r x := by rw [← scaled]; exact last
    have tpos : 0 < t := by
      rcases mul_pos_iff.mp product with positive | negative
      · exact positive.1
      · exact (not_lt_of_ge first.le negative.2).elim
    have straight : InnerProductGeometry.angle x y = 0 :=
      InnerProductGeometry.angle_eq_zero_iff.mpr ⟨xne, t, tpos, expression⟩
    rw [straight, expression, InnerProductGeometry.angle_smul_right_of_pos _ _ tpos,
      sub_self, abs_zero]
  · have sum := angle_add_of_orient_nonneg rne xne first.le last.le positive
    have difference : InnerProductGeometry.angle r x - InnerProductGeometry.angle r y =
        -InnerProductGeometry.angle x y := by linarith
    rw [difference, abs_neg, abs_of_nonneg (InnerProductGeometry.angle_nonneg x y)]

/-- Reverse triangle inequality for genuine angular distances, including degenerate directions. -/
theorem abs_angle_sub_angle_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r a b : E) :
    |InnerProductGeometry.angle r a - InnerProductGeometry.angle r b| ≤
      InnerProductGeometry.angle a b := by
  have first := InnerProductGeometry.angle_le_angle_add_angle r a b
  have last := InnerProductGeometry.angle_le_angle_add_angle r b a
  rw [InnerProductGeometry.angle_comm b a] at last
  apply abs_le.mpr
  constructor <;> linarith

/-- Matching the seam angles and the same-side condition bounds an opened planar section turn. -/
theorem hinge_section_angle_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r x y : Plane} (first : 0 < orient 0 r x) (last : 0 < orient 0 r y)
    (edge a b : E)
    (first_angle : InnerProductGeometry.angle r x = InnerProductGeometry.angle edge a)
    (last_angle : InnerProductGeometry.angle r y = InnerProductGeometry.angle edge b) :
    InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle a b := by
  rw [angle_eq_abs_sub_of_same_halfplane first last, first_angle, last_angle]
  exact abs_angle_sub_angle_le edge a b

end Unfoldings
