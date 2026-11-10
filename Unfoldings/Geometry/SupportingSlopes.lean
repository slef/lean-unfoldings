module

public import Unfoldings.Geometry.MeshProgress

/-!
# Supporting slopes of a concave function

Different contact points have supporting-slope regions with disjoint interiors.
This elementary dual separation result does not need differentiability or a
supplied area formula. It is useful for planar normal images of convex caps.
-/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Slopes of upper supporting affine functions, with the sign convention for a concave roof. -/
def supportingSlopes (f : E → ℝ) (p : E) : Set E :=
  {g | ∀ q, f q ≤ f p - inner ℝ g (q - p)}

theorem convex_supportingSlopes (f : E → ℝ) (p : E) : Convex ℝ (supportingSlopes f p) := by
  intro g hg h hh a b ha hb sum q
  have first := mul_le_mul_of_nonneg_left (hg q) ha
  have last := mul_le_mul_of_nonneg_left (hh q) hb
  simp only [inner_add_left, real_inner_smul_left]
  change f q ≤ f p - (a * inner ℝ g (q - p) + b * inner ℝ h (q - p))
  nlinarith [congrArg (fun r : ℝ => r * f p) sum,
    congrArg (fun r : ℝ => r * f q) sum]

/-- Supporting slopes form a monotone relation after negating the concave roof. -/
theorem supportingSlopes_monotone (f : E → ℝ) (p q g h : E)
    (first : g ∈ supportingSlopes f p) (last : h ∈ supportingSlopes f q) :
    0 ≤ inner ℝ (g - h) (p - q) := by
  have one := first q
  have two := last p
  have reversed : q - p = -(p - q) := by abel
  rw [reversed, inner_neg_right] at one
  rw [inner_sub_left]
  linarith

/-- Actual supporting-slope regions at distinct points have disjoint interiors. -/
theorem supportingSlopes_interiors_disjoint (f : E → ℝ) {p q : E} (different : p ≠ q) :
    Disjoint (interior (supportingSlopes f p)) (interior (supportingSlopes f q)) := by
  apply Set.disjoint_left.mpr
  intro g first last
  obtain ⟨a, positive, nearby⟩ := exists_positive_ray_mem g (q - p) (supportingSlopes f p)
    (mem_interior_iff_mem_nhds.mp first)
  have monotone := supportingSlopes_monotone f p q (g + a • (q - p)) g nearby (interior_subset last)
  rw [add_sub_cancel_left, real_inner_smul_left] at monotone
  have reversed : q - p = -(p - q) := by abel
  rw [reversed, inner_neg_left, real_inner_self_eq_norm_sq] at monotone
  have strict := mul_pos positive (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr different)))
  linarith

end Unfoldings
