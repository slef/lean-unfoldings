module

public import Unfoldings.Roof.TentNormals
public import Unfoldings.Geometry.SupportedPlane

/-! Proper roof completions retain old planes and construct new rigid Euclidean planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Every original support plane uses its original rigid placement and actual normal. -/
def supportPlane (f : Face) : SpatialPlane where
  height := K.supportHeight f
  place := K.folding.place f
  project := K.projectFaceEquiv f
  horizontal_place _ := rfl
  height_place x := (K.supportHeight_face f x).symm
  normal := K.normal f
  normal_unit := K.normal_unit f
  normal_upward := K.normal_upward f
  normal_tangent := K.normal_tangent f

/-- All planes of the completed roof have actual isometric coordinates and upward unit normals. -/
def completionPlanes (H L : ℝ) : Face ⊕ (Bool × Bool) → SpatialPlane :=
  Sum.elim K.supportPlane (fun s => SpatialPlane.ofGraph H (tentSlope L s))

@[simp] theorem completionPlanes_original_place (H L : ℝ) (f : Face) :
    (K.completionPlanes H L (.inl f)).place = K.folding.place f := rfl

theorem completionPlanes_height (H L : ℝ) (i : Face ⊕ (Bool × Bool)) :
    (K.completionPlanes H L i).height = K.tentCompletionSupport H L i := by
  cases i with
  | inl f => rfl
  | inr s =>
    ext p
    exact (tentSupport_eq_inner H L s p).symm

@[simp] theorem completionPlanes_normal (H L : ℝ) (i : Face ⊕ (Bool × Bool)) :
    (K.completionPlanes H L i).normal = K.tentCompletionNormal L i := by
  cases i <;> rfl

/-- The actual physical plane family has precisely the completed affine roof as its envelope. -/
theorem completionPlanes_envelope (H L : ℝ) (p : Plane) :
    AffineEnvelope.height (fun i => (K.completionPlanes H L i).height) p =
      K.tentCompletionHeight H L p := by
  have same : (fun i => (K.completionPlanes H L i).height) = K.tentCompletionSupport H L :=
    funext (K.completionPlanes_height H L)
  rw [same]
  rfl

theorem completionPlanes_tilt {φ : ℝ} (positive : 0 < φ) (small : φ < Real.pi / 2)
    (tilt : K.TiltBound φ) (H : ℝ) (i : Face ⊕ (Bool × Bool)) :
    Real.cos φ ≤ (K.completionPlanes H (Real.sin φ / 2) i).normal 2 := by
  rw [K.completionPlanes_normal]
  exact K.tentCompletionNormal_tilt positive small tilt i

end Unfoldings.ConvexRoof
