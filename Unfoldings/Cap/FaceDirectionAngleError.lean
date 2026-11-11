module

public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Cap.AcuteProjection

/-! Actual face-direction angle error, with a uniform positive tilt threshold. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Actual tangent-direction angle distortion relative to horizontal projection. -/
def FaceDirectionAngleError (ε : ℝ) : Prop :=
  ∀ f (a b : Plane), a ≠ 0 → b ≠ 0 →
    |InnerProductGeometry.angle a b -
      InnerProductGeometry.angle (K.spatialDirection f a) (K.spatialDirection f b)| ≤ ε

/-- Rigid development gives the same actual angle error, regardless of overlap. -/
theorem faceDirectionAngleError_developed {ε : ℝ} (error : K.FaceDirectionAngleError ε)
    {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
    (f : Face) (a b : Plane) (ane : a ≠ 0) (bne : b ≠ 0) :
    |InnerProductGeometry.angle a b - InnerProductGeometry.angle
      (D.developedDirection K f a) (D.developedDirection K f b)| ≤ ε := by
  rw [D.developedDirection_angle]
  exact error f a b ane bne

/-- The same numerical tilt threshold works before the complete input mesh is specified. -/
theorem exists_uniform_tilt_faceDirectionAngleError {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ → K.FaceDirectionAngleError ε := by
  obtain ⟨φ, bounds, estimate⟩ := Cap.exists_projection_angle_tilt positive
  refine ⟨φ, bounds, fun K tilt f a b ane bne => ?_⟩
  have result := estimate (K.normal f) (K.spatialDirection f a) (K.spatialDirection f b)
    (K.normal_unit f) (tilt f) (K.spatialDirection_ne_zero f ane) (K.spatialDirection_ne_zero f bne)
    (K.spatialDirection_tangent f a) (K.spatialDirection_tangent f b)
  rw [K.horizontal_spatialDirection, K.horizontal_spatialDirection] at result
  exact result.le

end Unfoldings.ConvexCap
