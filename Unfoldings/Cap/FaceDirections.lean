module

public import Unfoldings.Cap.GermSupports
public import Unfoldings.Cap.SectionAngles
public import Unfoldings.Development

/-!
# Actual face directions over prescribed horizontal directions

Inverse projection determines a genuine tangent vector on each original face.
Its spatial image is the section vector with slope supplied by the actual face
normal. Every actual development supplies its rigid planar image; local angle
estimates therefore apply to those real developed vectors.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def pullbackDirection (f : Face) (direction : Plane) : Plane :=
  (K.projectFaceEquiv f).linear.symm direction

def spatialDirection (f : Face) (direction : Plane) : Space :=
  (K.folding.place f).linear (K.pullbackDirection f direction)

@[simp] theorem horizontal_spatialDirection (f : Face) (direction : Plane) :
    Cap.horizontal (K.spatialDirection f direction) = direction := by
  change (K.projectFaceEquiv f).linear ((K.projectFaceEquiv f).linear.symm direction) = direction
  exact (K.projectFaceEquiv f).linear.apply_symm_apply direction

theorem spatialDirection_tangent (f : Face) (direction : Plane) :
    inner ℝ (K.normal f) (K.spatialDirection f direction) = 0 :=
  K.normal_tangent f (K.pullbackDirection f direction)

theorem spatialDirection_height (f : Face) (direction : Plane) :
    K.spatialDirection f direction 2 = -inner ℝ (K.normalSlope f) direction := by
  have identity := K.normalSlope_inner_add_height f (K.spatialDirection f direction)
  rw [K.horizontal_spatialDirection, K.spatialDirection_tangent, mul_zero] at identity
  linarith

/-- The tangent vector is the actual vertical-section direction dictated by the support plane. -/
theorem spatialDirection_eq_section (f : Face) (direction : Plane) :
    K.spatialDirection f direction =
      Cap.horizontalAtHeight direction (-inner ℝ (K.normalSlope f) direction) := by
  have horizontal := K.horizontal_spatialDirection f direction
  ext i
  fin_cases i
  · exact congrArg (fun p : Plane => p 0) horizontal
  · exact congrArg (fun p : Plane => p 1) horizontal
  · exact K.spatialDirection_height f direction

theorem spatialDirection_ne_zero (f : Face) {direction : Plane} (nonzero : direction ≠ 0) :
    K.spatialDirection f direction ≠ 0 := by
  intro zero
  have horizontal := K.horizontal_spatialDirection f direction
  rw [zero, map_zero] at horizontal
  exact nonzero horizontal.symm

/-- Genuine bending of section tangents depends on the real support-plane inclinations. -/
theorem spatialDirection_angle (f g : Face) (direction : Plane) (unit : ‖direction‖ = 1) :
    InnerProductGeometry.angle (K.spatialDirection f direction) (K.spatialDirection g direction) =
      |Real.arctan (-inner ℝ (K.normalSlope g) direction) -
        Real.arctan (-inner ℝ (K.normalSlope f) direction)| := by
  rw [K.spatialDirection_eq_section, K.spatialDirection_eq_section]
  exact Cap.angle_horizontalAtHeight direction unit _ _

end Unfoldings.ConvexCap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

def developedDirection (f : Face) (direction : Plane) : Plane :=
  (D.place f).linear (K.pullbackDirection f direction)

theorem developedDirection_ne_zero (f : Face) {direction : Plane} (nonzero : direction ≠ 0) :
    D.developedDirection K f direction ≠ 0 := by
  have pullback_ne : K.pullbackDirection f direction ≠ 0 := by
    change (K.projectFaceEquiv f).linear.symm direction ≠ 0
    simpa only [map_zero] using (K.projectFaceEquiv f).linear.symm.injective.ne nonzero
  change (D.place f).toAffineIsometry.linearIsometry (K.pullbackDirection f direction) ≠ 0
  simpa only [map_zero] using (D.place f).toAffineIsometry.linearIsometry.injective.ne pullback_ne

/-- Actual rigid developments preserve the actual spatial angles of all face directions. -/
theorem developedDirection_angle (f : Face) (a b : Plane) :
    InnerProductGeometry.angle (D.developedDirection K f a) (D.developedDirection K f b) =
      InnerProductGeometry.angle (K.spatialDirection f a) (K.spatialDirection f b) := by
  calc
    _ = InnerProductGeometry.angle (K.pullbackDirection f a) (K.pullbackDirection f b) :=
      (D.place f).toAffineIsometry.linearIsometry.angle_map _ _
    _ = _ := ((K.folding.place f).linearIsometry.angle_map _ _).symm

/-- The uniform projection estimate controls actual developed vectors in every direction. -/
theorem developedDirection_projection_error {ε φ : ℝ}
    (estimate : ∀ normal a b : Space, ‖normal‖ = 1 → Real.cos φ ≤ normal 2 →
      a ≠ 0 → b ≠ 0 → inner ℝ normal a = 0 → inner ℝ normal b = 0 →
      |InnerProductGeometry.angle (Cap.horizontal a) (Cap.horizontal b) -
        InnerProductGeometry.angle a b| < ε)
    (tilt : K.TiltBound φ) (f : Face) (a b : Plane) (ane : a ≠ 0) (bne : b ≠ 0) :
    |InnerProductGeometry.angle a b -
      InnerProductGeometry.angle (D.developedDirection K f a)
        (D.developedDirection K f b)| < ε := by
  have bound := estimate (K.normal f) (K.spatialDirection f a) (K.spatialDirection f b)
    (K.normal_unit f) (tilt f) (K.spatialDirection_ne_zero f ane) (K.spatialDirection_ne_zero f bne)
    (K.spatialDirection_tangent f a) (K.spatialDirection_tangent f b)
  rw [K.horizontal_spatialDirection, K.horizontal_spatialDirection,
    ← D.developedDirection_angle K] at bound
  exact bound

end Unfoldings.FacewiseDevelopment
