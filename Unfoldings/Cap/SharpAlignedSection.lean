module

public import Unfoldings.Cap.SharpSectionHinge
public import Unfoldings.Cap.AlignedSectionTurn

/-! Transfer the sharp local hinge estimate to actual planar bank alignments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- The residual turn of an actual aligned opening is bounded by the
extrinsic turn times the sine of the cap tilt. -/
theorem aligned_section_angle_le_sin_tilt
    {phi : ℝ} (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (connected : C.DuallyConnected retain) (s : C.Seam) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (oriented : ∀ a b, orient 0 (R a) (R b) = orient 0 a b)
    (aligns : R (D.developedDirection K (C.right s).face (K.projectedSeamVector s)) =
      D.developedDirection K (C.left s).face (K.projectedSeamVector s))
    (direction : Plane)
    (transverse : orient 0 (K.projectedSeamVector s) direction ≠ 0) :
    angle (D.developedDirection K (C.left s).face direction)
      (R (D.developedDirection K (C.right s).face direction)) ≤
        sin phi * angle (K.spatialDirection (C.left s).face direction)
          (K.spatialDirection (C.right s).face direction) := by
  rw [D.aligned_section_angle_eq_abs_sub K connected s R oriented aligns direction transverse]
  exact K.abs_spatialDirection_seam_angle_sub_le_sin_tilt_of_transverse nonnegative small tilt
    s direction transverse

end Unfoldings.FacewiseDevelopment
