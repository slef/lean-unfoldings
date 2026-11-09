module

public import Unfoldings.Geometry.SpatialHinge

/-! Distinct supporting planes make the opposite corner strictly lie on its side. -/

@[expose] public section

namespace Unfoldings

theorem strict_opposite_of_distinct_support_planes (T : Triangle) (e : Fin 3)
    (left right : Plane →ᵃⁱ[ℝ] Space) (f : Space →L[ℝ] ℝ) (a : ℝ)
    (nonzero : f ≠ 0) (right_level : ∀ p, f (right p) = a)
    (edge_level : ∀ x : T.Edge e, f (left x.val) = a)
    (supported : f (left (T.opposite e)) ≤ a)
    (different : LinearMap.range left.linear ≠ LinearMap.range right.linear) :
    f (left (T.opposite e)) < a := by
  apply lt_of_le_of_ne supported
  intro equal
  let height : Plane →ᵃ[ℝ] ℝ :=
    f.toLinearMap.toAffineMap.comp left.toAffineMap - AffineMap.const ℝ Plane a
  have zero (x : T.Edge e) : height x.val = 0 := sub_eq_zero.mpr (edge_level x)
  have left_level (p : Plane) : f (left p) = a := by
    have formula := T.affine_height_eq_coord e height
      (zero ⟨_, left_mem_segment ℝ _ _⟩) (zero ⟨_, right_mem_segment ℝ _ _⟩) p
    change f (left p) - a = (f (left (T.opposite e)) - a) * _ at formula
    rw [equal, sub_self, zero_mul] at formula
    exact sub_eq_zero.mp formula
  exact different ((affineIsometry_linear_range_eq_kernel left f nonzero a left_level).trans
    (affineIsometry_linear_range_eq_kernel right f nonzero a right_level).symm)

end Unfoldings
