module

public import Unfoldings.Cap.Flat
public import Unfoldings.Cap.Boundary
public import Unfoldings.Cap.AcuteProjection
public import Unfoldings.Geometry.EdgeSides

/-!
# The cap with no interior vertices

The horizontal rim contains every original corner. Affine rigidity then puts
every whole face in that plane. The actual cap is flat and its uncut projection
is an injective nonoverlapping development, regardless of the mesh angles.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

def vertical : Space →ₗ[ℝ] ℝ where
  toFun v := v 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Unfoldings.Cap

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  (boundary : ∀ v : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ v)

include boundary in
theorem all_face_heights_zero (f : Face) (x : Plane) : K.folding.place f x 2 = 0 := by
  let height : Plane →ᵃ[ℝ] ℝ := Cap.vertical.toAffineMap.comp (K.folding.place f).toAffineMap
  have equal : height = AffineMap.const ℝ Plane 0 := by
    apply (C.triangle f).affine_ext
    intro i
    let v := C.vertexOfCorner Set.univ (f, i)
    exact K.height_eq_zero_of_bankBoundary (C.vertexPoint Set.univ v)
      ((C.vertexPoint_mem_bankBoundary_iff Set.univ v).mpr (boundary v))
  exact congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A x) equal

include boundary in
theorem normal_height_one_of_no_interior (f : Face) : K.normal f 2 = 1 := by
  obtain ⟨x, first⟩ := K.projectFace_surjective f (Cap.horizontal (K.normal f))
  obtain ⟨y, last⟩ := K.projectFace_surjective f 0
  have tangent := K.normal_tangent_chord f x y
  rw [Cap.horizontal_inner, map_sub] at tangent
  change inner ℝ (Cap.horizontal (K.normal f)) (K.projectFace f x - K.projectFace f y) +
    K.normal f 2 * (K.folding.place f x 2 - K.folding.place f y 2) = 0 at tangent
  rw [first, last, K.all_face_heights_zero boundary, K.all_face_heights_zero boundary,
    sub_zero, sub_self, mul_zero, add_zero, real_inner_self_eq_norm_sq] at tangent
  have zero : ‖Cap.horizontal (K.normal f)‖ = 0 := (sq_eq_zero_iff).mp tangent
  have identity := Cap.horizontal_norm_sq (K.normal f)
  rw [K.normal_unit f, zero] at identity
  nlinarith [K.normal_upward f]

include boundary in
theorem flat_of_no_interior : K.TiltBound 0 := by
  intro f
  rw [Real.cos_zero, K.normal_height_one_of_no_interior boundary f]

def noInteriorDevelopment : FacewiseDevelopment C Set.univ :=
  K.flatDevelopment (K.flat_of_no_interior boundary)

theorem noInteriorDevelopment_nonoverlapping : (K.noInteriorDevelopment boundary).Nonoverlapping :=
  K.flatDevelopment_nonoverlapping (K.flat_of_no_interior boundary)

theorem noInteriorDevelopment_injective :
    Function.Injective (K.noInteriorDevelopment boundary).toPlane :=
  K.flatDevelopment_injective (K.flat_of_no_interior boundary)

end Unfoldings.ConvexCap
