module

public import Unfoldings.Cap.Basic

/-! Smaller nonnegative tilt thresholds satisfy every larger threshold below pi. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Shrinking the allowed normal tilt strengthens the same geometric hypothesis. -/
theorem TiltBound.of_le {φ ψ : ℝ} (bound : K.TiltBound φ) (nonnegative : 0 ≤ φ)
    (large : ψ ≤ Real.pi) (ordered : φ ≤ ψ) : K.TiltBound ψ :=
  fun f => (Real.cos_le_cos_of_nonneg_of_le_pi nonnegative large ordered).trans (bound f)

end Unfoldings.ConvexCap
