module

public import Unfoldings.Geometry.ConvexSegmentExit
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! Proper affine support levels cannot pass through the interior of a supported set. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The set need not be convex. A nonzero affine functional nonnegative on it
can vanish only outside its interior. Constant nonzero functionals are allowed. -/
theorem not_mem_interior_of_affine_lower_bound {s : Set E} (f : E →ᵃ[ℝ] ℝ)
    (proper : f ≠ 0) (lower : ∀ p ∈ s, 0 ≤ f p) {x : E} (zero : f x = 0) :
    x ∉ interior s := by
  intro inside
  apply proper
  apply AffineMap.ext_on (isOpen_interior.affineSpan_eq_top ⟨x, inside⟩)
  intro p hp
  change f p = 0
  have nonnegative := lower p (interior_subset hp)
  by_contra unequal
  have positive : 0 < f p := lt_of_le_of_ne nonnegative (Ne.symm unequal)
  obtain ⟨a, after, in_region⟩ := exists_lineMap_beyond_one_mem (q := p) inside
  have bound := lower _ in_region
  rw [f.apply_lineMap, AffineMap.lineMap_apply_ring, zero] at bound
  nlinarith [mul_pos (sub_pos.mpr after) positive]

end Unfoldings
