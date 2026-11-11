module

public import Unfoldings.Cap.DevelopmentOrientation
public import Unfoldings.Cap.SeamDirections
public import Unfoldings.Geometry.HingeTurnBound

/-!
# Actual section turns across retained original seams

Opposite-side development and actual projection imply the common-halfplane
condition for every transverse direction. Opening the retained hinge therefore
cannot increase the genuine spatial section turn.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- The actual developed section vectors occupy the same strict side of a retained seam. -/
theorem developedDirection_seam_sides (s : C.Seam) (kept : s ∈ retain)
    (direction : Plane) (transverse : orient 0 (K.projectedSeamVector s) direction ≠ 0) :
    0 < orient 0 (D.developedDirection K (C.left s).face (K.projectedSeamVector s))
        (D.developedDirection K (C.left s).face direction) *
      orient 0 (D.developedDirection K (C.left s).face (K.projectedSeamVector s))
        (D.developedDirection K (C.right s).face direction) := by
  rw [D.developedDirection_orient K]
  rw [D.developedDirection_seam K s kept, D.developedDirection_orient K]
  have positive := mul_pos (D.projectedPlacement_scales_mul_pos K s kept)
    (sq_pos_of_ne_zero transverse)
  nlinarith only [positive]

/-- For actual retained cap hinges, rigid planar opening contracts section turning. -/
theorem retained_section_angle_le (s : C.Seam) (kept : s ∈ retain)
    (direction : Plane) (transverse : orient 0 (K.projectedSeamVector s) direction ≠ 0) :
    InnerProductGeometry.angle (D.developedDirection K (C.left s).face direction)
        (D.developedDirection K (C.right s).face direction) ≤
      InnerProductGeometry.angle (K.spatialDirection (C.left s).face direction)
        (K.spatialDirection (C.right s).face direction) := by
  apply hinge_section_angle_le_of_product_pos
    (D.developedDirection_seam_sides K s kept direction transverse)
    (K.spatialDirection (C.left s).face (K.projectedSeamVector s))
  · exact D.developedDirection_angle K _ _ _
  · rw [D.developedDirection_seam K s kept, K.spatialDirection_seam]
    exact D.developedDirection_angle K _ _ _

end Unfoldings.FacewiseDevelopment
