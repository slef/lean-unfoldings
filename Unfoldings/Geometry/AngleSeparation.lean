module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Strict angle inequalities through a transverse direction

A linear functional vanishing on the two boundary directions and nonzero
on the intermediate direction excludes equality in the angular triangle
inequality, provided the two boundary directions are not opposite. Applied
to a vertex-figure plane, the apex direction is transverse to that plane.
-/

@[expose] public section

open scoped NNReal

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem angle_lt_angle_add_angle_of_transverse (f : E →L[ℝ] ℝ) (x y z : E)
    (left : f x = 0) (right : f z = 0) (transverse : f y ≠ 0)
    (not_opposite : InnerProductGeometry.angle x z ≠ Real.pi) :
    InnerProductGeometry.angle x z <
      InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by
  have y_nonzero : y ≠ 0 := by
    intro zero
    exact transverse (by rw [zero, map_zero])
  have not_equal : InnerProductGeometry.angle x z ≠
      InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by
    intro equal
    rcases (InnerProductGeometry.angle_eq_angle_add_angle_iff y_nonzero).mp equal with
      opposite | generated
    · exact not_opposite opposite
    · let K := f.toLinearMap.ker.restrictScalars ℝ≥0
      have contained : Submodule.span ℝ≥0 ({x, z} : Set E) ≤ K := by
        apply Submodule.span_le.mpr
        intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact left
        · exact right
      exact transverse (contained generated)
  exact lt_of_le_of_ne (InnerProductGeometry.angle_le_angle_add_angle x y z) not_equal

end Unfoldings
