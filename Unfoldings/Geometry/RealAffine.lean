module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Two distinct real parameters determine an affine map. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem real_affine_ext (f g : ℝ →ᵃ[ℝ] E) {a b : ℝ} (different : a ≠ b)
    (first : f a = g a) (last : f b = g b) : f = g := by
  apply AffineMap.ext
  intro x
  have nonzero : b - a ≠ 0 := sub_ne_zero.mpr different.symm
  have representation : AffineMap.lineMap a b ((x - a) / (b - a)) = x := by
    rw [AffineMap.lineMap_apply_ring']
    field_simp
    ring
  calc
    f x = f (AffineMap.lineMap a b ((x - a) / (b - a))) := congrArg f representation.symm
    _ = g (AffineMap.lineMap a b ((x - a) / (b - a))) := by
      rw [f.apply_lineMap, g.apply_lineMap, first, last]
    _ = g x := congrArg g representation

end Unfoldings
