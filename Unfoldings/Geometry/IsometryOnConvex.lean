module

public import Mathlib.Analysis.Convex.StrictConvexBetween

/-! Isometric embeddings of convex subsets preserve all segment parameters. -/

@[expose] public section

namespace Unfoldings

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]

theorem isometry_lineMap_on_convex {s : Set E} (convex : Convex ℝ s)
    (f : s → F) (isometry : Isometry f) (x y : s) (t : ℝ) (inside : t ∈ Set.Icc (0 : ℝ) 1) :
    f ⟨AffineMap.lineMap x.val y.val t, convex.lineMap_mem x.property y.property inside⟩ =
      AffineMap.lineMap (f x) (f y) t := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rw [isometry.dist_eq, isometry.dist_eq]
    change dist x.val (AffineMap.lineMap x.val y.val t) = t * dist x.val y.val
    rw [dist_left_lineMap, Real.norm_of_nonneg inside.1]
  · rw [isometry.dist_eq, isometry.dist_eq]
    change dist (AffineMap.lineMap x.val y.val t) y.val = (1 - t) * dist x.val y.val
    rw [dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.mpr inside.2)]

end Unfoldings
