module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Data.Finset.Max

/-!
# A finite list cannot be straight at every chosen corner

At a farthest listed point from any fixed center, a straight angle would
put that point strictly between two listed points. Strict convexity of
Euclidean distance rules this out. No polygon embedding is required.
-/

@[expose] public section

namespace Unfoldings

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Finite ι] [Nonempty ι]

theorem exists_corner_angle_ne_pi (base : ι → E) (prev next : ι → ι) (center : E) :
    ∃ i, EuclideanGeometry.angle (base (prev i)) (base i) (base (next i)) ≠ Real.pi := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i, _member, maximal⟩ := Finset.exists_max_image Finset.univ
    (fun i => dist (base i) center) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro straight
  have between := EuclideanGeometry.angle_eq_pi_iff_sbtw.mp straight
  have strict := between.dist_lt_max_dist center
  exact (lt_irrefl _ (strict.trans_le
    (max_le (maximal _ (Finset.mem_univ _)) (maximal _ (Finset.mem_univ _)))))

end Unfoldings
