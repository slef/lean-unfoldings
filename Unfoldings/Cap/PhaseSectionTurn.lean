module

public import Unfoldings.Cap.ParentDirectionRotation
public import Unfoldings.Geometry.ComplexHingeTurn

/-!
# Actual section turns after a signed complex bank rotation

All faces use the same projection-preserving frame. A known rigid seam rotation
is removed from the target face's section direction; its remaining turn is
bounded by the actual spatial bend. Curvature rotations can then be summed with
their signs instead of being charged once per crossed edge.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Any transverse projected pair has the same strict complex area sign on all actual faces. -/
theorem projectionContour_frame_sides (D : FacewiseDevelopment C M.retain)
    (f g : Face) (a b : Plane) (nonzero : orient 0 a b ≠ 0) :
    0 < (starRingEnd ℂ
        (D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K f a)) *
        D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K f b)).im *
      (starRingEnd ℂ
        (D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K g a)) *
        D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K g b)).im := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have reverse : orient 0 b a = -orient 0 a b := by unfold orient; ring
    have first := M.projectionContour_frame_positive D f b a (by rw [reverse]; linarith)
    have last := M.projectionContour_frame_positive D g b a (by rw [reverse]; linarith)
    have swap (x y : ℂ) : (starRingEnd ℂ y * x).im = -(starRingEnd ℂ x * y).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [swap] at first last
    exact mul_pos_of_neg_of_neg (neg_pos.mp first) (neg_pos.mp last)
  · exact mul_pos (M.projectionContour_frame_positive D f a b positive)
      (M.projectionContour_frame_positive D g a b positive)

/-- Removing the actual signed seam phase leaves no more turn than the actual spatial bend. -/
theorem section_angle_le_of_frame_rotation (D : FacewiseDevelopment C M.retain)
    (f g : Face) (edge : Plane)
    (shared : K.spatialDirection f edge = K.spatialDirection g edge)
    (κ : ℝ)
    (rotation : D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K g edge) =
      polarRay κ *
        D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K f edge))
    (direction : Plane) (transverse : orient 0 edge direction ≠ 0) :
    InnerProductGeometry.angle
        (D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K f direction))
        (polarRay (-κ) *
          D.boundaryCycleFrame M.projectionContour.cycle (D.developedDirection K g direction)) ≤
      InnerProductGeometry.angle (K.spatialDirection f direction)
        (K.spatialDirection g direction) := by
  let L := D.boundaryCycleFrame M.projectionContour.cycle
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
    exact M.projectionContour_frame_sides D f g edge direction transverse
  · exact (L.toLinearIsometry.angle_map _ _).trans (D.developedDirection_angle K _ _ _)
  · rw [← aligns, Complex.angle_mul_left (polarRay_ne_zero _), shared]
    exact (L.toLinearIsometry.angle_map _ _).trans (D.developedDirection_angle K _ _ _)

/-- Actual parent banks have the curvature-corrected local turn bound in one global frame. -/
theorem exists_parent_section_turn_bound (D : FacewiseDevelopment C M.retain)
    (e : C.Vertex Set.univ) (nonroot : e ∉ M.parents.roots) :
    ∃ enter leave : Fin (M.projectionContour.length + 1), ∃ side : Bool,
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point enter)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) side ∧
      (C.boundaryEndEquiv M.retain (M.projectionContour.cycle.point leave)).1 =
        C.relativeCutBank M.retain Set.univ (C.selectedParentCut M.selection e nonroot) (!side) ∧
      ¬ C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e enter ∧
      C.SubtreeBoundaryInside M.selection M.projectionContour.cycle e leave ∧
      ∀ direction : Plane,
        orient 0 (K.projectedVertex (M.parents.parent e) - K.projectedVertex e) direction ≠ 0 →
        InnerProductGeometry.angle
          (D.boundaryCycleFrame M.projectionContour.cycle
            (D.developedDirection K (M.projectionContour.cycle.point enter).val.1.1 direction))
          (polarRay (-M.subtreeCurvature e) *
            D.boundaryCycleFrame M.projectionContour.cycle
              (D.developedDirection K (M.projectionContour.cycle.point leave).val.1.1 direction)) ≤
          InnerProductGeometry.angle
            (K.spatialDirection (M.projectionContour.cycle.point enter).val.1.1 direction)
            (K.spatialDirection (M.projectionContour.cycle.point leave).val.1.1 direction) := by
  obtain ⟨enter, leave, side, first, last, outside, inside, rotation⟩ :=
    M.exists_parent_direction_rotation D e nonroot
  have shared := K.spatialDirection_parent_banks M.selection e nonroot
    (M.projectionContour.cycle.point enter) (M.projectionContour.cycle.point leave)
    side first last outside inside
  refine ⟨enter, leave, side, first, last, outside, inside, fun direction transverse => ?_⟩
  exact M.section_angle_le_of_frame_rotation D _ _ _ shared _ rotation direction transverse

end Unfoldings.ConvexCap.SectorForest
