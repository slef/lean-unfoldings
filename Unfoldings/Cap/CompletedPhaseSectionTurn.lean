module

public import Unfoldings.Cap.CompletedParentDirections
public import Unfoldings.Geometry.ComplexHingeTurn

/-! Curvature-corrected section turns for completed roof forests in one global frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

/-- Any transverse projected pair has the same strict complex area sign on all actual faces. -/
theorem projectionContour_frame_sides (D : FacewiseDevelopment C R.completedRetain)
    (f g : Face) (a b : Plane) (nonzero : orient 0 a b ≠ 0) :
    0 < (starRingEnd ℂ
        (D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f a)) *
        D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f b)).im *
      (starRingEnd ℂ
        (D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K g a)) *
        D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K g b)).im := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have reverse : orient 0 b a = -orient 0 a b := by unfold orient; ring
    have first := R.completedContour_frame_positive D f b a (by rw [reverse]; linarith)
    have last := R.completedContour_frame_positive D g b a (by rw [reverse]; linarith)
    have swap (x y : ℂ) : (starRingEnd ℂ y * x).im = -(starRingEnd ℂ x * y).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [swap] at first last
    exact mul_pos_of_neg_of_neg (neg_pos.mp first) (neg_pos.mp last)
  · exact mul_pos (R.completedContour_frame_positive D f a b positive)
      (R.completedContour_frame_positive D g a b positive)

/-- Removing the actual signed seam phase leaves no more turn than the actual spatial bend. -/
theorem section_angle_le_of_frame_rotation (D : FacewiseDevelopment C R.completedRetain)
    (f g : Face) (edge : Plane)
    (shared : K.spatialDirection f edge = K.spatialDirection g edge)
    (κ : ℝ)
    (rotation : D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K g edge) =
      polarRay κ *
        D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f edge))
    (direction : Plane) (transverse : orient 0 edge direction ≠ 0) :
    InnerProductGeometry.angle
        (D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K f direction))
        (polarRay (-κ) *
          D.boundaryCycleFrame R.completedContour.cycle (D.developedDirection K g direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection f direction)
        (K.spatialDirection g direction) := by
  let L := D.boundaryCycleFrame R.completedContour.cycle
  have aligns : polarRay (-κ) * L (D.developedDirection K g edge) =
      L (D.developedDirection K f edge) := by
    rw [rotation, ← mul_assoc, ← polarRay_add, neg_add_cancel, polarRay_zero, one_mul]
  have last_cross : (starRingEnd ℂ (L (D.developedDirection K f edge)) *
        (polarRay (-κ) * L (D.developedDirection K g direction))).im =
      (starRingEnd ℂ (L (D.developedDirection K g edge)) *
        L (D.developedDirection K g direction)).im := by
    rw [← aligns]
    exact complex_cross_mul_unit _ _ _ (norm_polarRay _)
  apply complex_hinge_section_angle_le_of_product_pos
    (edge := K.spatialDirection f edge)
  · rw [last_cross]
    exact R.projectionContour_frame_sides D f g edge direction transverse
  · exact (L.toLinearIsometry.angle_map _ _).trans (D.developedDirection_angle K _ _ _)
  · rw [← aligns, Complex.angle_mul_left (polarRay_ne_zero _), shared]
    exact (L.toLinearIsometry.angle_map _ _).trans (D.developedDirection_angle K _ _ _)

end Unfoldings.ConvexCap.RadialCutForest
