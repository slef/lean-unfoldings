module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSide

/-! A physical one-sided roof germ determines every actual incident cell's support. -/

@[expose] public section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A)

/-- A full-dimensional original cell meeting a local one-sided affine roof germ uses
that same supporting height whenever its original cut side agrees. -/
theorem incident_support_eq_of_side_germ (anchor a : A) (f : Plane →ᵃ[ℝ] ℝ)
    (signs : A → Bool)
    (aligned : ∀ c z, z ∈ P.footprint c → 0 ≤ AffineArrangement.signed f (signs c) z)
    {p : Plane} (member : p ∈ P.footprint a) (same_side : signs a = signs anchor)
    {U : Set Plane} (open_U : IsOpen U) (inside : p ∈ U)
    (germ : ∀ z ∈ U, 0 ≤ AffineArrangement.signed f (signs anchor) z →
      height family z = (family (P.support anchor)).height z) :
    (family (P.support a)).height = (family (P.support anchor)).height := by
  have approached : p ∈ closure (interior (P.footprint a)) := by
    rw [(P.convex a).closure_interior_eq_closure_of_nonempty_interior (P.full a),
      (P.closed a).closure_eq]
    exact member
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp open_U p inside
  obtain ⟨q, in_cell, near⟩ := Metric.mem_closure_iff.mp approached ε positive
  have in_region : q ∈ U := ball (Metric.mem_ball.mpr (by rwa [dist_comm]))
  apply AffineMap.ext_on ((isOpen_interior.inter open_U).affineSpan_eq_top
    (show (interior (P.footprint a) ∩ U).Nonempty from ⟨q, in_cell, in_region⟩))
  intro z hz
  apply (P.active a z (interior_subset hz.1)).symm.trans
  apply germ z hz.2
  simpa only [same_side] using aligned a z (interior_subset hz.1)

end Unfoldings.SpatialEnvelope.WholePartition
