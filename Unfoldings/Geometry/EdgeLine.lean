module

public import Unfoldings.Geometry.EdgeSides

/-! Affine agreement on a full triangle edge extends to its supporting line. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem eq_lineMap_of_coord_zero (T : Triangle) (e : Fin 3) (x : Plane)
    (zero : T.coord (next (next e)) x = 0) :
    x = AffineMap.lineMap (T.vertex e) (T.vertex (next e)) (T.coord (next e) x) := by
  have sum := T.coord_sum_edge e x
  have expression := T.reconstruct_edge e x
  rw [zero, zero_smul, add_zero] at expression
  have coefficient : T.coord e x = 1 - T.coord (next e) x := by linarith
  rw [coefficient, ← AffineMap.lineMap_apply_module] at expression
  exact expression

theorem affine_eq_of_coord_zero (T : Triangle) (e : Fin 3)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (f g : Plane →ᵃ[ℝ] V)
    (left : f (T.vertex e) = g (T.vertex e))
    (right : f (T.vertex (next e)) = g (T.vertex (next e)))
    (x : Plane) (zero : T.coord (next (next e)) x = 0) : f x = g x := by
  have expression := T.eq_lineMap_of_coord_zero e x zero
  calc
    f x = f (AffineMap.lineMap (T.vertex e) (T.vertex (next e))
        (T.coord (next e) x)) := congrArg f expression
    _ = g (AffineMap.lineMap (T.vertex e) (T.vertex (next e))
        (T.coord (next e) x)) := by rw [f.apply_lineMap, g.apply_lineMap, left, right]
    _ = g x := congrArg g expression.symm

end Unfoldings.Triangle
