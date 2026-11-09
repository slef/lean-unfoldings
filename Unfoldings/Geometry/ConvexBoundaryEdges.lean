module

public import Unfoldings.Geometry.AffineMaximum
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Supporting boundary segments and interior centers

A segment on a closed convex boundary has one supporting functional at
both endpoints. Every interior point is strictly below that level, so a
nondegenerate boundary edge and an interior center are noncollinear. These
facts also apply to collinear subdivisions of a polygon's maximal edges.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {s : Set E}

theorem exists_supporting_functional_of_boundary_segment (convex : Convex ℝ s)
    (closed : IsClosed s) (nonempty : (interior s).Nonempty) {a b : E}
    (edge : segment ℝ a b ⊆ frontier s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ z ∈ s, f z ≤ f a) ∧ f b = f a ∧
      ∀ z ∈ interior s, f z < f a := by
  let m := midpoint ℝ a b
  have boundary : m ∈ frontier s := edge (midpoint_mem_segment _ _)
  obtain ⟨f, nonzero, supported⟩ := geometric_hahn_banach_of_nonempty_interior_point
    convex boundary.2 nonempty
  have ha : a ∈ s := closed.closure_eq ▸ (edge (left_mem_segment ℝ _ _)).1
  have hb : b ∈ s := closed.closure_eq ▸ (edge (right_mem_segment ℝ _ _)).1
  have left := supported a ha
  have right := supported b hb
  have average : f m = (f a + f b) / 2 := by
    have mapped := f.toLinearMap.toAffineMap.map_midpoint a b
    change f (midpoint ℝ a b) = midpoint ℝ (f a) (f b) at mapped
    simpa only [m, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, inv_mul_eq_div] using mapped
  have at_a : f m = f a := by linarith
  have at_b : f b = f a := by linarith
  refine ⟨f, nonzero, ?_, at_b, ?_⟩
  · intro z hz
    exact (supported z hz).trans_eq at_a
  · intro z hz
    exact supporting_functional_lt_on_interior f nonzero s (f a)
      (fun z hz => (supported z hz).trans_eq at_a) z hz

theorem not_collinear_of_boundary_segment (convex : Convex ℝ s) (closed : IsClosed s)
    {a b x : E} (inside : x ∈ interior s) (different : a ≠ b)
    (edge : segment ℝ a b ⊆ frontier s) : ¬ Collinear ℝ ({a, x, b} : Set E) := by
  obtain ⟨f, _nonzero, _supported, same, strict⟩ :=
    exists_supporting_functional_of_boundary_segment convex closed ⟨x, inside⟩ edge
  intro collinear
  have in_span := collinear.mem_affineSpan_of_mem_of_ne
    (p₁ := a) (p₂ := b) (p₃ := x) (by simp) (by simp) (by simp) different
  obtain ⟨t, image⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp in_span
  have mapped := f.toLinearMap.toAffineMap.apply_lineMap a b t
  change f (AffineMap.lineMap a b t) = AffineMap.lineMap (f a) (f b) t at mapped
  rw [image, same, AffineMap.lineMap_same] at mapped
  exact (strict x inside).ne mapped

end Unfoldings
