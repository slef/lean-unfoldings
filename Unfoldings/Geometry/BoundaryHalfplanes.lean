module

public import Unfoldings.Geometry.ConvexBoundaryEdges
public import Unfoldings.Geometry.PlanarCollinearity
public import Unfoldings.Geometry.EdgeSides

/-!
# A convex planar boundary edge supports the whole set

The supporting functional of the edge is a positive multiple of its
opposite barycentric coordinate in a triangle with an interior center.
Thus every point lies on the same weak side of the edge as that center.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem orient_ne_zero_of_boundary_segment {s : Set Plane}
    (convex : Convex ℝ s) (closed : IsClosed s) {a b x : Plane}
    (inside : x ∈ interior s) (different : a ≠ b)
    (edge : segment ℝ a b ⊆ frontier s) : orient a b x ≠ 0 := by
  have noncollinear := not_collinear_of_boundary_segment convex closed inside different edge
  intro zero
  apply noncollinear
  have collinear := (orient_eq_zero_iff_collinear a b x).mp zero
  have sets : ({a, b, x} : Set Plane) = {a, x, b} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rwa [sets] at collinear

theorem orient_mul_nonneg_of_boundary_segment {s : Set Plane}
    (convex : Convex ℝ s) (closed : IsClosed s) {a b x z : Plane}
    (inside : x ∈ interior s) (different : a ≠ b)
    (edge : segment ℝ a b ⊆ frontier s) (member : z ∈ s) :
    0 ≤ orient a b z * orient a b x := by
  have nonzero := orient_ne_zero_of_boundary_segment convex closed inside different edge
  let T : Triangle := ⟨![a, b, x], nonzero⟩
  obtain ⟨f, _nonzero, supported, same, strict⟩ :=
    exists_supporting_functional_of_boundary_segment convex closed ⟨x, inside⟩ edge
  let height : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane (f a) - f.toLinearMap.toAffineMap
  have left : height (T.vertex 0) = 0 := sub_self _
  have right : height (T.vertex (Triangle.next 0)) = 0 := sub_eq_zero.mpr same.symm
  have coordinate := T.affine_height_eq_coord 0 height left right z
  change f a - f z = (f a - f x) * T.coord 2 z at coordinate
  have positive : 0 < f a - f x := sub_pos.mpr (strict x inside)
  have nonnegative : 0 ≤ T.coord 2 z := by
    have bound := supported z member
    nlinarith
  have area := T.orient_eq_coord_mul 0 z
  change orient a b z = orient a b x * T.coord 2 z at area
  rw [area]
  calc
    0 ≤ (orient a b x) ^ 2 * T.coord 2 z := mul_nonneg (sq_nonneg _) nonnegative
    _ = _ := by ring

end Unfoldings
