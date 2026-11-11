module

public import Unfoldings.Cap.FaceDirectionAngleError
public import Unfoldings.Cap.SectionHeadingBound
public import Unfoldings.Geometry.RelativeAngleBound

/-!
# Uniform agreement of all actual developed face directions

The section construction aligns one direction on each face with the common rim
face. Consistent projection orientation and the actual local projection-angle
estimate transfer that alignment to every nonzero direction on every face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- One actual reference direction controls all directions of two actual original faces. -/
theorem face_direction_angle_le_of_reference (D : FacewiseDevelopment C M.retain)
    {ε B : ℝ} (error : K.FaceDirectionAngleError ε) (f g : Face)
    (reference direction : Plane) (rne : reference ≠ 0) (dne : direction ≠ 0)
    (aligned : InnerProductGeometry.angle (D.developedDirection K f reference)
      (D.developedDirection K g reference) ≤ B) :
    InnerProductGeometry.angle (D.developedDirection K f direction)
      (D.developedDirection K g direction) ≤ B + 2 * ε := by
  let L := D.boundaryCycleFrame M.projectionContour.cycle
  let F : Plane →ₗ[ℝ] ℂ :=
    L.toLinearEquiv.toLinearMap.comp (D.projectedPlacement K f).linear.toLinearMap
  let G : Plane →ₗ[ℝ] ℂ :=
    L.toLinearEquiv.toLinearMap.comp (D.projectedPlacement K g).linear.toLinearMap
  have frameF (a b : Plane) : InnerProductGeometry.angle (F a) (F b) =
      InnerProductGeometry.angle (D.developedDirection K f a) (D.developedDirection K f b) :=
    L.toLinearIsometry.angle_map _ _
  have frameG (a b : Plane) : InnerProductGeometry.angle (G a) (G b) =
      InnerProductGeometry.angle (D.developedDirection K g a) (D.developedDirection K g b) :=
    L.toLinearIsometry.angle_map _ _
  have genuine (h : Face) (v : Plane) (nonzero : v ≠ 0) :
      L (D.developedDirection K h v) ≠ 0 := by
    simpa only [map_zero] using L.injective.ne (D.developedDirection_ne_zero K h nonzero)
  have comparison : InnerProductGeometry.angle (F direction) (G direction) ≤ B + ε + ε := by
    apply linear_relative_angle_le F G rne dne
      (genuine f reference rne) (genuine g reference rne) (genuine g direction dne)
    · exact (L.toLinearIsometry.angle_map _ _).le.trans aligned
    · rw [frameF]
      exact K.faceDirectionAngleError_developed error D f reference direction rne dne
    · rw [frameG]
      exact K.faceDirectionAngleError_developed error D g reference direction rne dne
    · intro transverse
      exact M.projectionContour_frame_sides D f g reference direction transverse
  have frames : InnerProductGeometry.angle (F direction) (G direction) =
      InnerProductGeometry.angle (D.developedDirection K f direction)
        (D.developedDirection K g direction) := L.toLinearIsometry.angle_map _ _
  rw [frames] at comparison
  linarith

/-- Every direction of every original face agrees uniformly with the same original rim face. -/
theorem face_direction_angle_le_anchor (D : FacewiseDevelopment C M.retain)
    (positive : 0 < t) (small : t < 1) (A : K.RimAnchor) (f : Face)
    {φ ε : ℝ} (nonnegative : 0 ≤ φ) (tilt_small : φ < Real.pi / 2) (tilt : K.TiltBound φ)
    (error : K.FaceDirectionAngleError ε) (direction : Plane) (dne : direction ≠ 0) :
    InnerProductGeometry.angle (D.developedDirection K A.bank.val.face direction)
      (D.developedDirection K f direction) ≤
        2 * φ + 2 * C.totalInteriorAngularDefect Set.univ + 2 * ε := by
  obtain ⟨q, _inside, different, aligned⟩ :=
    M.exists_face_section_angle D positive small A f nonnegative tilt_small tilt
  exact M.face_direction_angle_le_of_reference D error A.bank.val.face f
    (q - A.point) direction (sub_ne_zero.mpr different) dne aligned

end Unfoldings.ConvexCap.SectorForest
