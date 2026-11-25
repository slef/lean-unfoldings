module

public import Unfoldings.Roof.ClippedPhysicalCurvature
public import Unfoldings.Roof.ComponentClippedExtension
public import Unfoldings.Convex.PolygonSideDirections

/-! Any finite half-plane selector supplies its finite physical support model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonSideDirections

universe u

variable {I : Type} [Fintype I] [Nonempty I]

/-- The affine slacks at the polygon sides. -/
def affineSides (normal : I → Plane) (offset : I → ℝ) (i : ULift.{u} I) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane (offset i.down) - (innerSL ℝ (normal i.down)).toLinearMap.toAffineMap

theorem clip_affineSides (normal : I → Plane) (offset : I → ℝ) :
    AffineEnvelope.clip (affineSides.{u} normal offset) 0 =
      {p | ∀ i, inner ℝ (normal i) p ≤ offset i} := by
  ext p
  constructor
  · intro member i
    have bound := member.trans (AffineEnvelope.height_le (affineSides.{u} normal offset) p ⟨i⟩)
    change 0 ≤ offset i - inner ℝ (normal i) p at bound
    exact sub_nonneg.mp bound
  · intro member
    obtain ⟨i, equal⟩ :=
      AffineEnvelope.exists_height_eq (affineSides.{u} normal offset) p
    change 0 ≤ AffineEnvelope.height (affineSides.{u} normal offset) p
    rw [equal]
    exact sub_nonneg.mpr (member i.down)

theorem affineSides_height_pos (normal : I → Plane) (offset : I → ℝ) {reference : Plane}
    (strict : ∀ i, inner ℝ (normal i) reference < offset i) :
    0 < AffineEnvelope.height (affineSides.{u} normal offset) reference := by
  obtain ⟨i, equal⟩ := AffineEnvelope.exists_height_eq (affineSides.{u} normal offset) reference
  rw [equal]
  exact sub_pos.mpr (strict i.down)

end Unfoldings.PolygonSideDirections

namespace Unfoldings.ConvexRoof

open PolygonSideDirections

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C) {I : Type} [Fintype I] [Nonempty I]
  {slopes : Set Plane} (B : PolygonSideDirections I slopes)
  (compact : IsCompact slopes) (nonempty : slopes.Nonempty)

include B in
/-- The clipped extension over a finite polygon is given by actual spatial planes. -/
theorem exists_finiteSlopeModel_of_polygon :
    Nonempty (K.clippedExtension slopes compact nonempty).FiniteSlopeModel := by
  obtain ⟨normal, offset, _, reference, strict, carrier⟩ := B
  have equal := (clip_affineSides.{u} normal offset).trans carrier.symm
  clear carrier
  subst slopes
  exact ⟨K.clippedPhysicalModel (affineSides.{u} normal offset) compact
    (affineSides_height_pos.{u} normal offset strict)⟩

include B in
/-- Use the same polygon construction on one selected component, retaining
its actual intercepts and the original normals. -/
theorem exists_componentFiniteSlopeModel_of_polygon {U : Set Face} (present : U.Nonempty) :
    Nonempty (K.componentClippedExtension present compact nonempty).FiniteSlopeModel := by
  obtain ⟨normal, offset, _, reference, strict, carrier⟩ := B
  have equal := (clip_affineSides.{u} normal offset).trans carrier.symm
  clear carrier
  subst slopes
  exact ⟨K.componentClippedPhysicalModel present (affineSides.{u} normal offset) compact
    (affineSides_height_pos.{u} normal offset strict)⟩

end Unfoldings.ConvexRoof
