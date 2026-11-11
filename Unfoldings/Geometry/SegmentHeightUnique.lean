module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith

/-! A strictly increasing linear height uniquely parametrizes a whole straight segment. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem linear_segment_bounds (height : E →ₗ[ℝ] ℝ) {a b x : E}
    (ordered : height a ≤ height b) (member : x ∈ segment ℝ a b) :
    height x ∈ Set.Icc (height a) (height b) := by
  have inside : height x ∈ segment ℝ (height a) (height b) :=
    (image_segment ℝ height.toAffineMap a b).subset ⟨x, member, rfl⟩
  rwa [segment_eq_Icc ordered] at inside

theorem point_eq_of_mem_segment_of_linear_eq (height : E →ₗ[ℝ] ℝ) {a b x y : E}
    (genuine : height a < height b) (first : x ∈ segment ℝ a b)
    (last : y ∈ segment ℝ a b) (equal : height x = height y) : x = y := by
  obtain ⟨s, _, at_x⟩ := (segment_eq_image_lineMap ℝ a b).subset first
  obtain ⟨t, _, at_y⟩ := (segment_eq_image_lineMap ℝ a b).subset last
  have coordinates : s * (height b - height a) + height a =
      t * (height b - height a) + height a := by
    rw [← at_x, ← at_y, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
      map_add, map_add, map_smul, map_smul, map_sub] at equal
    exact equal
  have parameters : s = t := by nlinarith
  exact at_x.symm.trans ((congrArg (AffineMap.lineMap a b) parameters).trans at_y)

end Unfoldings
