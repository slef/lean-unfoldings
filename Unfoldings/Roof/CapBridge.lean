module

public import Unfoldings.Roof.Basic
public import Unfoldings.Cap.Basic

/-! Every horizontal-rim convex cap is an arbitrary-rim convex roof on the same complex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- Forget boundary-height normalization, preserving every face, seam, and physical placement. -/
def toRoof (K : ConvexCap C) : ConvexRoof C where
  folding := K.folding
  normal := K.normal
  normal_unit := K.normal_unit
  normal_upward := K.normal_upward
  normal_tangent := K.normal_tangent
  supporting := K.supporting
  projection_injective := K.projection_injective
  convex_projection := K.convex_projection
  interior_projection := K.interior_projection

@[simp] theorem toRoof_footprint (K : ConvexCap C) : K.toRoof.footprint = K.footprint := rfl

@[simp] theorem toRoof_tiltBound (K : ConvexCap C) (φ : ℝ) :
    K.toRoof.TiltBound φ ↔ K.TiltBound φ := Iff.rfl

end Unfoldings.ConvexCap
