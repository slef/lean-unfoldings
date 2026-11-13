module

public import Unfoldings.Roof.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Monotonicity of the geometric normal tilt bound for arbitrary-rim roofs. -/

@[expose] public section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem TiltBound.of_le {φ θ : ℝ} (bound : K.TiltBound φ) (nonnegative : 0 ≤ φ)
    (small : θ ≤ Real.pi) (ordered : φ ≤ θ) : K.TiltBound θ := fun f =>
  (Real.cos_le_cos_of_nonneg_of_le_pi nonnegative small ordered).trans (bound f)

end Unfoldings.ConvexRoof
