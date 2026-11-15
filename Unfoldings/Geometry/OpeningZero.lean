module

public import Unfoldings.Geometry.PolygonalRayOpening

/-! A zero opening retains the exact original chain and infinite bank. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ n)

@[simp] theorem rotateSuffix_zero (hinge : Fin (n + 1)) : P.rotateSuffix hinge 0 = P := by
  apply congrArg (PolygonalChain.mk (E := ℂ) (n := n))
  funext i
  split_ifs
  · rfl
  · simp only [complexRotation_apply, polarRay_zero, one_mul]
    abel

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

@[simp] theorem rotateSuffix_zero (hinge : Fin (n + 1)) : R.rotateSuffix hinge 0 = R := by
  have chain := R.chain.rotateSuffix_zero hinge
  have direction : (R.rotateSuffix hinge 0).direction = R.direction := by
    change complexRotation 0 R.direction = R.direction
    simp only [complexRotation_apply, polarRay_zero, one_mul]
  exact congrArg₂ (PolygonalRay.mk (E := ℂ) (n := n)) chain direction

end Unfoldings.PolygonalRay
