module

public import Unfoldings.Geometry.ComplexRotation
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Affine.Isometry

/-! Actual source-fixed rotations as affine isometric equivalences. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def sourceRotation (source : ℂ) (angle : ℝ) : ℂ ≃ᵃⁱ[ℝ] ℂ :=
  (AffineIsometryEquiv.constVAdd ℝ ℂ (-source)).trans
    ((rotation (Circle.exp angle)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.constVAdd ℝ ℂ source))

@[simp] theorem sourceRotation_apply (source : ℂ) (angle : ℝ) (z : ℂ) :
    sourceRotation source angle z = source + complexRotation angle (z - source) := by
  change source + polarRay angle * (-source + z) = source + polarRay angle * (z - source)
  ring

end Unfoldings
