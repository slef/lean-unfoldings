module

public import Unfoldings.Geometry.EdgeSides

/-! An affine function vanishing on a line has one consistent sign on either halfplane. -/

@[expose] public section

namespace Unfoldings

/-- One noncollinear test point determines an affine function on its entire side of a line. -/
theorem affine_nonnegative_on_line_side (g : Plane →ᵃ[ℝ] ℝ) (p q c : Plane)
    (nondegenerate : orient p q c ≠ 0) (first : g p = 0) (last : g q = 0)
    (test : 0 ≤ g c) {x : Plane} (same_side : 0 ≤ orient p q x * orient p q c) : 0 ≤ g x := by
  let T : Triangle := ⟨![p, q, c], nondegenerate⟩
  have values := T.affine_height_eq_coord 0 g first last x
  change g x = g c * T.coord 2 x at values
  have orientations := T.orient_eq_coord_mul 0 x
  change orient p q x = orient p q c * T.coord 2 x at orientations
  have product : g x * orient p q c ^ 2 = g c * (orient p q x * orient p q c) := by
    rw [values, orientations]
    ring
  have nonnegative : 0 ≤ g x * orient p q c ^ 2 := by
    rw [product]
    exact mul_nonneg test same_side
  exact nonneg_of_mul_nonneg_left nonnegative (sq_pos_of_ne_zero nondegenerate)

/-- The signed halfplane containing a strict test point inherits its affine lower bound. -/
theorem affine_nonnegative_on_signed_side (g : Plane →ᵃ[ℝ] ℝ) (p q c : Plane)
    (first : g p = 0) (last : g q = 0) (test : 0 ≤ g c) (side : Bool)
    (strict : 0 < if side then orient p q c else -orient p q c)
    {x : Plane} (weak : 0 ≤ if side then orient p q x else -orient p q x) : 0 ≤ g x := by
  have nondegenerate : orient p q c ≠ 0 := by
    cases side
    · exact (neg_pos.mp strict).ne
    · exact strict.ne'
  apply affine_nonnegative_on_line_side g p q c nondegenerate first last test
  cases side
  · change 0 < -orient p q c at strict
    change 0 ≤ -orient p q x at weak
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonneg.mp weak) (neg_pos.mp strict).le
  · exact mul_nonneg weak strict.le

end Unfoldings
