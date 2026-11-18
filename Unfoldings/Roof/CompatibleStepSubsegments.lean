module

public import Unfoldings.Roof.CompatiblePotentialPaths

/-! Actual compatible routing steps survive every ordered closed forward subsegment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem followsStep_subsegment {x y : Plane} (step : R.FollowsStep x y)
    (s t : unitInterval) (forward : s ≤ t) :
    R.FollowsStep (AffineMap.lineMap x y s.val) (AffineMap.lineMap x y t.val) := by
  have interpolates (origin d : Plane) (u v w : ℝ) :
      AffineMap.lineMap (origin + u • d) (origin + v • d) w =
        origin + (AffineMap.lineMap u v w) • d := by
    simp only [AffineMap.lineMap_apply_module']
    module
  have ordered (u v : ℝ) (before : u ≤ v) :
      Monotone (fun w : ℝ => AffineMap.lineMap u v w) := by
    intro w z h
    simp only [AffineMap.lineMap_apply_module', smul_eq_mul]
    exact add_le_add_left (mul_le_mul_of_nonneg_right h (sub_nonneg.mpr before)) u
  rcases step with ⟨v, u, w, nonnegative, before, upper, rfl, rfl⟩ |
    ⟨r, u, w, nonnegative, before, rfl, rfl⟩
  · have first : 0 ≤ AffineMap.lineMap u w s.val := nonnegative.trans
      (by simpa only [AffineMap.lineMap_apply_zero] using ordered u w before s.property.1)
    have last : AffineMap.lineMap u w t.val ≤ 1 := by
      have bound : AffineMap.lineMap u w t.val ≤ w := by
        simpa only [AffineMap.lineMap_apply_one] using ordered u w before t.property.2
      exact bound.trans upper
    exact Or.inl ⟨v, AffineMap.lineMap u w s.val, AffineMap.lineMap u w t.val,
      first, ordered u w before forward, last, interpolates _ _ _ _ _, interpolates _ _ _ _ _⟩
  · have first : 0 ≤ AffineMap.lineMap u w s.val := nonnegative.trans
      (by simpa only [AffineMap.lineMap_apply_zero] using ordered u w before s.property.1)
    refine Or.inr ⟨r, AffineMap.lineMap u w s.val, AffineMap.lineMap u w t.val,
      first, ordered u w before forward, ?_, ?_⟩
    · exact interpolates _ _ _ _ _
    · exact interpolates _ _ _ _ _

end Unfoldings.ConvexRoof.CompatiblePotentialRouting
