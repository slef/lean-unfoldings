module

public import Unfoldings.Geometry.TriangleRadial

/-! Closed triangle radial coordinates, with a separate apex case. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Every closed triangle point other than the apex lies on a positive ray to its opposite edge. -/
theorem point_on_opposite_edge_ray (T : Triangle) {x : Plane}
    (inside : x ∈ T.carrier) (different : x ≠ T.vertex 0) :
    ∃ z ∈ segment ℝ (T.vertex 1) (T.vertex 2), ∃ a ∈ Set.Ioc (0 : ℝ) 1,
      x = T.vertex 0 + a • (z - T.vertex 0) := by
  have nonnegative := T.carrier_eq_nonneg_coord.le inside
  have sum := T.sum_coord x
  rw [Fin.sum_univ_three] at sum
  let a := T.coord 1 x + T.coord 2 x
  have a_nonnegative : 0 ≤ a := add_nonneg (nonnegative 1) (nonnegative 2)
  have a_positive : 0 < a := by
    by_contra not_positive
    have zero : a = 0 := le_antisymm (le_of_not_gt not_positive) a_nonnegative
    have first : T.coord 1 x = 0 := by
      dsimp only [a] at zero
      linarith [nonnegative 1, nonnegative 2]
    have last : T.coord 2 x = 0 := by
      dsimp only [a] at zero
      linarith [nonnegative 1, nonnegative 2]
    have origin : T.coord 0 x = 1 := by linarith
    have expression := T.reconstruct_edge 0 x
    change x = T.coord 0 x • T.vertex 0 + T.coord 1 x • T.vertex 1 +
      T.coord 2 x • T.vertex 2 at expression
    simp only [first, last, origin, one_smul, zero_smul, add_zero] at expression
    exact different expression
  have a_le : a ≤ 1 := by dsimp only [a]; linarith [nonnegative 0]
  let t := T.coord 2 x / a
  have t_nonnegative : 0 ≤ t := div_nonneg (nonnegative 2) a_positive.le
  have t_le : t ≤ 1 := (div_le_one a_positive).mpr (by
    dsimp only [a]
    linarith [nonnegative 1, nonnegative 2])
  let z := AffineMap.lineMap (T.vertex 1) (T.vertex 2) t
  refine ⟨z, lineMap_mem_segment ℝ _ _ ⟨t_nonnegative, t_le⟩,
    a, ⟨a_positive, a_le⟩, ?_⟩
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
