module

public import Unfoldings.Cap.RetainedSectionTurn

/-!
# Actual section turns after rigid bank alignment

This estimate also applies across cut seams: align their actual directed bank
vectors by an orientation-preserving rotation in the fixed global plane, then
compare the section turn with its genuine spatial turn. The amount and sign of
the alignment rotation are separate from this local hinge estimate.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- An actual bank alignment contracts transverse section turning, even across a cut. -/
theorem aligned_section_angle_le (connected : C.DuallyConnected retain)
    (s : C.Seam) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (oriented : ∀ a b, orient 0 (R a) (R b) = orient 0 a b)
    (aligns : R (D.developedDirection K (C.right s).face (K.projectedSeamVector s)) =
      D.developedDirection K (C.left s).face (K.projectedSeamVector s))
    (direction : Plane) (transverse : orient 0 (K.projectedSeamVector s) direction ≠ 0) :
    InnerProductGeometry.angle (D.developedDirection K (C.left s).face direction)
        (R (D.developedDirection K (C.right s).face direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection (C.left s).face direction)
        (K.spatialDirection (C.right s).face direction) := by
  have sides : 0 <
      orient 0 (D.developedDirection K (C.left s).face (K.projectedSeamVector s))
        (D.developedDirection K (C.left s).face direction) *
      orient 0 (D.developedDirection K (C.left s).face (K.projectedSeamVector s))
        (R (D.developedDirection K (C.right s).face direction)) := by
    rw [D.developedDirection_orient K, ← aligns, oriented, D.developedDirection_orient K]
    have positive := mul_pos
      (D.projectedPlacement_scales_mul_pos_of_connected K connected
        (C.left s).face (C.right s).face) (sq_pos_of_ne_zero transverse)
    nlinarith only [positive]
  apply hinge_section_angle_le_of_product_pos sides
    (K.spatialDirection (C.left s).face (K.projectedSeamVector s))
  · exact D.developedDirection_angle K _ _ _
  · rw [← aligns, K.spatialDirection_seam]
    exact (R.toLinearIsometry.angle_map _ _).trans (D.developedDirection_angle K _ _ _)

end Unfoldings.FacewiseDevelopment
