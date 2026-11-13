module

public import Unfoldings.Roof.ProjectedFaces
public import Unfoldings.Development

/-! Actual developed face charts over the horizontal coordinates of an arbitrary-rim roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexRoof C)

/-- Pull a horizontal vector back to its actual Euclidean face, then develop it rigidly. -/
def roofDirection (f : Face) (direction : Plane) : Plane :=
  (D.place f).linear ((K.projectFaceEquiv f).linear.symm direction)

def roofPlacement (f : Face) : Plane ≃ᵃ[ℝ] Plane :=
  (K.projectFaceEquiv f).symm.trans (D.place f).toAffineEquiv

@[simp] theorem roofPlacement_apply (f : Face) (x : Plane) :
    D.roofPlacement K f (K.projectFace f x) = D.place f x := by
  change D.place f ((K.projectFaceEquiv f).symm ((K.projectFaceEquiv f) x)) = D.place f x
  rw [AffineEquiv.symm_apply_apply]

@[simp] theorem roofPlacement_linear (f : Face) (direction : Plane) :
    (D.roofPlacement K f).linear direction = D.roofDirection K f direction := rfl

theorem roofDirection_chord (f : Face) (a b : Plane) :
    D.roofDirection K f (K.projectFace f b - K.projectFace f a) = D.place f b - D.place f a := by
  have linear := (K.projectFaceEquiv f).toAffineMap.linear_apply_vsub b a
  change (K.projectFaceEquiv f).linear (b - a) = K.projectFace f b - K.projectFace f a at linear
  rw [roofDirection, ← linear, LinearEquiv.symm_apply_apply]
  exact (D.place f).toAffineEquiv.toAffineMap.linear_apply_vsub b a

theorem roofDirection_ne_zero (f : Face) {direction : Plane} (nonzero : direction ≠ 0) :
    D.roofDirection K f direction ≠ 0 := by
  have pullback_ne : (K.projectFaceEquiv f).linear.symm direction ≠ 0 := by
    simpa only [map_zero] using (K.projectFaceEquiv f).linear.symm.injective.ne nonzero
  change (D.place f).toAffineIsometry.linearIsometry _ ≠ 0
  simpa only [map_zero] using (D.place f).toAffineIsometry.linearIsometry.injective.ne pullback_ne

theorem roofPlacement_image_interior (f : Face) :
    D.roofPlacement K f '' interior (K.projectedTriangle f).carrier =
      interior (D.faceImage f) := by
  let chart := (D.roofPlacement K f).toContinuousAffineEquiv.toHomeomorph
  have carrier : chart '' (K.projectedTriangle f).carrier = D.faceImage f := by
    change D.roofPlacement K f '' (K.projectedTriangle f).carrier = D.faceImage f
    simp only [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier,
      Set.image_image, D.roofPlacement_apply, faceImage]
  exact (chart.image_interior _).trans (congrArg interior carrier)

end Unfoldings.FacewiseDevelopment
