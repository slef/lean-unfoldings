module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.Angles

/-! The coordinate signed-area test agrees with affine collinearity. -/

@[expose] public section

namespace Unfoldings

theorem orient_eq_zero_iff_collinear (a b c : Plane) :
    orient a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set Plane) := by
  constructor
  · intro zero
    by_cases same : a = b
    · subst b
      simpa only [Set.insert_eq_of_mem (Set.mem_insert _ _)] using
        (collinear_pair ℝ a c)
    · obtain ⟨t, image⟩ := exists_lineMap_of_orient_eq_zero same zero
      have collinear : Collinear ℝ ({c, a, b} : Set Plane) :=
        collinear_insert_of_mem_affineSpan_pair
          (mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, image.symm⟩)
      have sets : ({c, a, b} : Set Plane) = {a, b, c} := by
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [sets] at collinear
  · intro collinear
    by_contra nonzero
    let T : Triangle := ⟨![a, b, c], nonzero⟩
    have impossible := T.not_collinear_corners 0
    change ¬ Collinear ℝ ({b, a, c} : Set Plane) at impossible
    exact impossible (Set.insert_comm b a {c} ▸ collinear)

end Unfoldings
