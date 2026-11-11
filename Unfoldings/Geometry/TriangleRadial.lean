module

public import Unfoldings.Geometry.EdgeSides
public import Mathlib.Tactic.FieldSimp

/-! Every interior triangle point lies strictly along a ray to the opposite open edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Radial coordinates from the first corner to the opposite open edge. -/
theorem interior_point_on_opposite_edge_ray (T : Triangle) {x : Plane}
    (inside : x ∈ interior T.carrier) :
    ∃ z ∈ openSegment ℝ (T.vertex 1) (T.vertex 2), ∃ a ∈ Set.Ioo (0 : ℝ) 1,
      x = T.vertex 0 + a • (z - T.vertex 0) := by
  have positive := T.interior_eq_pos_coord.le inside
  have sum := T.sum_coord x
  rw [Fin.sum_univ_three] at sum
  let a := T.coord 1 x + T.coord 2 x
  have a_positive : 0 < a := add_pos (positive 1) (positive 2)
  have a_less : a < 1 := by dsimp only [a]; linarith [positive 0]
  let t := T.coord 2 x / a
  have t_positive : 0 < t := div_pos (positive 2) a_positive
  have t_less : t < 1 := (div_lt_one a_positive).mpr (by dsimp only [a]; linarith [positive 1])
  let z := AffineMap.lineMap (T.vertex 1) (T.vertex 2) t
  refine ⟨z, lineMap_mem_openSegment ℝ _ _ ⟨t_positive, t_less⟩,
    a, ⟨a_positive, a_less⟩, ?_⟩
  have first : a * (1 - t) = T.coord 1 x := by
    dsimp only [t]
    field_simp
    dsimp only [a]
    ring
  have last : a * t = T.coord 2 x := by dsimp only [t]; field_simp
  have origin : 1 - a = T.coord 0 x := by dsimp only [a]; linarith
  have expanded : T.vertex 0 + a • (z - T.vertex 0) =
      (1 - a) • T.vertex 0 + (a * (1 - t)) • T.vertex 1 + (a * t) • T.vertex 2 := by
    dsimp only [z]
    rw [AffineMap.lineMap_apply_module]
    module
  rw [first, last, origin] at expanded
  exact (T.reconstruct_edge 0 x).trans expanded.symm

end Unfoldings.Triangle
