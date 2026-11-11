module

public import Unfoldings.Geometry.Affine

/-! A line avoiding an edge endpoint meets that edge only transversely. -/

@[expose] public section

namespace Unfoldings

/-- A nonconstant line meeting an edge line and avoiding its endpoint cannot be parallel to it. -/
theorem line_transverse_of_avoids_endpoint {a b p q : Plane} (edge : a ≠ b)
    (different : p ≠ q) (regular : ∀ t : ℝ, AffineMap.lineMap p q t ≠ a)
    (t : ℝ) (meets : orient a b (AffineMap.lineMap p q t) = 0) :
    orient 0 (b - a) (q - p) ≠ 0 := by
  intro parallel
  have difference : orient a b q - orient a b p = orient 0 (b - a) (q - p) := by
    simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
    ring
  have interpolate : orient a b (AffineMap.lineMap p q t) =
      (1 - t) * orient a b p + t * orient a b q := by
    rw [AffineMap.lineMap_apply_module']
    simp only [orient, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have first : orient a b p = 0 := by
    rw [parallel] at difference
    linear_combination meets - interpolate - t * difference
  have last : orient a b q = 0 := by rw [parallel] at difference; linarith
  obtain ⟨r, rfl⟩ := exists_lineMap_of_orient_eq_zero edge first
  obtain ⟨s, rfl⟩ := exists_lineMap_of_orient_eq_zero edge last
  have collinear : orient (AffineMap.lineMap a b r) (AffineMap.lineMap a b s) a = 0 := by
    simp only [AffineMap.lineMap_apply_module', orient, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    ring
  obtain ⟨u, image⟩ := exists_lineMap_of_orient_eq_zero different collinear
  exact regular u image.symm

end Unfoldings
