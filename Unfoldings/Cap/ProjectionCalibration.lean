module

public import Unfoldings.Cap.FaceDirectionAgreement

/-!
# One global developed frame calibrated to horizontal projection

A single rotation matches one direction of the fixed original rim face to its
projected direction. Consistent orientation and local angle distortion then
calibrate all directions of that face, while the actual section bound transfers
the calibration uniformly to every original face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Real rotation calibrating the common developed frame on one original rim-face direction. -/
def calibrationAngle (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference : Plane) : ℝ :=
  (Complex.orthonormalBasisOneI.repr.symm reference).arg -
    (D.boundaryCycleFrame M.projectionContour.cycle
      (D.developedDirection K A.bank.val.face reference)).arg

/-- One actual global planar isometry, fixed for all original faces and directions. -/
def calibratedFrame (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference : Plane) : Plane ≃ₗᵢ[ℝ] ℂ :=
  (D.boundaryCycleFrame M.projectionContour.cycle).trans
    (_root_.rotation (Circle.exp (M.calibrationAngle D A reference)))

theorem calibratedFrame_apply (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference v : Plane) :
    M.calibratedFrame D A reference v = polarRay (M.calibrationAngle D A reference) *
      D.boundaryCycleFrame M.projectionContour.cycle v := rfl

/-- Calibration matches the actual reference unit direction to the original projected one. -/
theorem calibratedFrame_reference (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference : Plane) (nonzero : reference ≠ 0) :
    NormedSpace.normalize
      (M.calibratedFrame D A reference (D.developedDirection K A.bank.val.face reference)) =
      NormedSpace.normalize (Complex.orthonormalBasisOneI.repr.symm reference) := by
  let L := D.boundaryCycleFrame M.projectionContour.cycle
  have developed : L (D.developedDirection K A.bank.val.face reference) ≠ 0 := by
    simpa only [map_zero] using L.injective.ne
      (D.developedDirection_ne_zero K A.bank.val.face nonzero)
  have projected : Complex.orthonormalBasisOneI.repr.symm reference ≠ 0 := by
    simpa only [map_zero] using Complex.orthonormalBasisOneI.repr.symm.injective.ne nonzero
  rw [M.calibratedFrame_apply, complex_normalize_mul,
    complex_normalize_eq_polar_arg developed, complex_normalize_eq_polar_arg projected]
  simp only [NormedSpace.normalize, norm_polarRay, inv_one, one_smul]
  rw [← polarRay_add]
  congr 1
  unfold calibrationAngle
  ring

/-- The same calibration preserves positive projection orientation on every actual face. -/
theorem calibratedFrame_positive (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference : Plane) (f : Face) (a b : Plane) (positive : 0 < orient 0 a b) :
    0 < (starRingEnd ℂ (M.calibratedFrame D A reference (D.developedDirection K f a)) *
      M.calibratedFrame D A reference (D.developedDirection K f b)).im := by
  rw [M.calibratedFrame_apply, M.calibratedFrame_apply,
    complex_cross_mul_unit _ _ _ (norm_polarRay _)]
  exact M.projectionContour_frame_positive D f a b positive

/-- Every transverse projected pair and calibrated actual face pair have the same area sign. -/
theorem calibratedFrame_projection_sides (D : FacewiseDevelopment C M.retain) (A : K.RimAnchor)
    (reference : Plane) (f : Face) (a b : Plane) (nonzero : orient 0 a b ≠ 0) :
    0 < (starRingEnd ℂ (M.calibratedFrame D A reference (D.developedDirection K f a)) *
      M.calibratedFrame D A reference (D.developedDirection K f b)).im * orient 0 a b := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · have reverse : orient 0 b a = -orient 0 a b := by unfold orient; ring
    have frame := M.calibratedFrame_positive D A reference f b a
      (by rw [reverse]; linarith)
    have swap (x y : ℂ) : (starRingEnd ℂ y * x).im = -(starRingEnd ℂ x * y).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [swap] at frame
    exact mul_pos_of_neg_of_neg (neg_pos.mp frame) negative
  · exact mul_pos (M.calibratedFrame_positive D A reference f a b positive) positive

/-- One reference calibration controls all anchor-face directions by the local angle error. -/
theorem calibrated_anchor_direction_angle_le (D : FacewiseDevelopment C M.retain)
    (A : K.RimAnchor) (reference : Plane) (nonzero : reference ≠ 0)
    {ε : ℝ} (error : K.FaceDirectionAngleError ε) (direction : Plane) (dne : direction ≠ 0) :
    InnerProductGeometry.angle
      (M.calibratedFrame D A reference (D.developedDirection K A.bank.val.face direction))
      (Complex.orthonormalBasisOneI.repr.symm direction) ≤ ε := by
  let R := M.calibratedFrame D A reference
  let P := Complex.orthonormalBasisOneI.repr.symm
  let F : Plane →ₗ[ℝ] ℂ :=
    R.toLinearEquiv.toLinearMap.comp (D.projectedPlacement K A.bank.val.face).linear.toLinearMap
  have original_ne (v : Plane) (hne : v ≠ 0) : P v ≠ 0 := by
    simpa only [map_zero] using P.injective.ne hne
  have actual_ne : F reference ≠ 0 := by
    change R (D.developedDirection K A.bank.val.face reference) ≠ 0
    simpa only [map_zero] using R.injective.ne
      (D.developedDirection_ne_zero K A.bank.val.face nonzero)
  have aligned : InnerProductGeometry.angle (F reference) (P reference) ≤ 0 := by
    have units : NormedSpace.normalize (F reference) = NormedSpace.normalize (P reference) :=
      M.calibratedFrame_reference D A reference nonzero
    have normalized_ne : NormedSpace.normalize (P reference) ≠ 0 := by
      rw [ne_eq, NormedSpace.normalize_eq_zero_iff]
      exact original_ne reference nonzero
    calc
      _ = InnerProductGeometry.angle (NormedSpace.normalize (F reference))
          (NormedSpace.normalize (P reference)) := by
        rw [InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right]
      _ = 0 := by rw [units, InnerProductGeometry.angle_self normalized_ne]
      _ ≤ _ := le_rfl
  have first_error : |InnerProductGeometry.angle reference direction -
      InnerProductGeometry.angle (F reference) (F direction)| ≤ ε := by
    have frame : InnerProductGeometry.angle (F reference) (F direction) =
        InnerProductGeometry.angle (D.developedDirection K A.bank.val.face reference)
          (D.developedDirection K A.bank.val.face direction) := R.toLinearIsometry.angle_map _ _
    rw [frame]
    exact K.faceDirectionAngleError_developed error D _ _ _ nonzero dne
  have last_error : |InnerProductGeometry.angle reference direction -
      InnerProductGeometry.angle (P reference) (P direction)| ≤ 0 := by
    have frame : InnerProductGeometry.angle (P reference) (P direction) =
        InnerProductGeometry.angle reference direction := P.toLinearIsometry.angle_map _ _
    rw [frame, sub_self, abs_zero]
  have sides (transverse : orient 0 reference direction ≠ 0) :
      0 < (starRingEnd ℂ (F reference) * F direction).im *
        (starRingEnd ℂ (P reference) * P direction).im := by
    have cross : (starRingEnd ℂ (P reference) * P direction).im = orient 0 reference direction := by
      have equal := orient_complex_repr_zero (P reference) (P direction)
      change orient 0 (P.symm (P reference)) (P.symm (P direction)) = _ at equal
      simpa only [P.symm_apply_apply] using equal.symm
    rw [cross]
    exact M.calibratedFrame_projection_sides D A reference _ _ _ transverse
  have result := linear_relative_angle_le F P.toLinearEquiv.toLinearMap nonzero dne actual_ne
    (original_ne reference nonzero) (original_ne direction dne) aligned first_error last_error sides
  simp only [zero_add, add_zero] at result
  exact result

/-- All actual face directions remain uniformly close to the original projected directions. -/
theorem calibrated_face_direction_angle_le (D : FacewiseDevelopment C M.retain)
    (positive : 0 < t) (small : t < 1) (A : K.RimAnchor)
    (reference : Plane) (nonzero : reference ≠ 0) (f : Face)
    {φ ε : ℝ} (nonnegative : 0 ≤ φ) (tilt_small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (error : K.FaceDirectionAngleError ε) (direction : Plane) (dne : direction ≠ 0) :
    InnerProductGeometry.angle
      (M.calibratedFrame D A reference (D.developedDirection K f direction))
      (Complex.orthonormalBasisOneI.repr.symm direction) ≤
        2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 3 * ε := by
  let R := M.calibratedFrame D A reference
  have agreement := M.face_direction_angle_le_anchor D positive small A f
    nonnegative tilt_small tilt error direction dne
  have calibration :=
    M.calibrated_anchor_direction_angle_le D A reference nonzero error direction dne
  have compare : InnerProductGeometry.angle (R (D.developedDirection K f direction))
      (R (D.developedDirection K A.bank.val.face direction)) ≤
        2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 2 * ε := by
    have frame : InnerProductGeometry.angle (R (D.developedDirection K f direction))
        (R (D.developedDirection K A.bank.val.face direction)) =
      InnerProductGeometry.angle (D.developedDirection K A.bank.val.face direction)
        (D.developedDirection K f direction) := by
      exact (R.toLinearIsometry.angle_map _ _).trans (InnerProductGeometry.angle_comm _ _)
    exact frame.le.trans agreement
  have triangle := InnerProductGeometry.angle_le_angle_add_angle
    (R (D.developedDirection K f direction))
    (R (D.developedDirection K A.bank.val.face direction))
    (Complex.orthonormalBasisOneI.repr.symm direction)
  linarith

end Unfoldings.ConvexCap.SectorForest
