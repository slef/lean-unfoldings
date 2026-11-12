module

public import Unfoldings.Cap.ClipSpatialTriangles
public import Unfoldings.Geometry.AffineEnd

/-! Fine roof triangles inside an original face have actual rigid coordinates in that face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

def originalCoordinates (i : T.Index) (f : Face) : Plane ≃ᵃ[ℝ] Plane :=
  (K.projectFaceEquiv (T.face i)).trans (K.projectFaceEquiv f).symm

theorem originalCoordinates_spatial (i : T.Index) (f : Face)
    (contained : (T.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) (x : Plane) :
    K.folding.place f (T.originalCoordinates i f x) = T.placement i x := by
  have on_face {x : Plane} (member : x ∈ (T.triangle i).carrier) :
      K.folding.place f (T.originalCoordinates i f x) = T.placement i x := by
    have projected : K.projectFace (T.face i) x ∈ (T.projectedTriangle i).carrier := by
      rw [T.triangle_carrier] at member
      obtain ⟨p, member, rfl⟩ := member
      simpa only [show K.projectFace (T.face i) = (K.projectFaceEquiv (T.face i)).toAffineMap
        from rfl, AffineEquiv.coe_toAffineMap, AffineEquiv.apply_symm_apply] using member
    have old := contained projected
    rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier] at old
    obtain ⟨y, inside, same⟩ := old
    have coordinates : T.originalCoordinates i f x = y := by
      change (K.projectFaceEquiv f).symm (K.projectFace (T.face i) x) = y
      rw [← same]
      exact (K.projectFaceEquiv f).symm_apply_apply y
    rw [coordinates, ← K.roofPoint_projectFace f ⟨y, inside⟩, same]
    exact (T.placement_eq_roofPoint i member).symm
  have maps : (K.folding.place f).toAffineMap.comp (T.originalCoordinates i f).toAffineMap =
      (T.placement i).toAffineMap := by
    apply (T.triangle i).affine_ext
    intro k
    exact on_face ((T.triangle i).vertex_mem k)
  exact congrArg (fun A : Plane →ᵃ[ℝ] Space => A x) maps

theorem originalCoordinates_isometry (i : T.Index) (f : Face)
    (contained : (T.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) :
    Isometry (T.originalCoordinates i f) := by
  intro x y
  calc
    edist (T.originalCoordinates i f x) (T.originalCoordinates i f y) =
        edist (K.folding.place f (T.originalCoordinates i f x))
          (K.folding.place f (T.originalCoordinates i f y)) :=
      ((K.folding.place f).isometry.edist_eq _ _).symm
    _ = edist (T.placement i x) (T.placement i y) := by
      rw [T.originalCoordinates_spatial i f contained x,
        T.originalCoordinates_spatial i f contained y]
    _ = edist x y := (T.placement i).isometry.edist_eq x y

def originalPlace (i : T.Index) (f : Face)
    (contained : (T.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  let A := (T.originalCoordinates_isometry i f contained).affineIsometryOfStrictConvexSpace
  { AffineEquiv.ofBijective (φ := A.toAffineMap)
      ⟨A.injective, (T.originalCoordinates i f).surjective⟩ with norm_map := A.norm_map }

@[simp] theorem originalPlace_apply (i : T.Index) (f : Face)
    (contained : (T.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) (x : Plane) :
    T.originalPlace i f contained x = T.originalCoordinates i f x := rfl

theorem originalPlace_projection (i : T.Index) (f : Face)
    (contained : (T.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) (x : Plane) :
    K.projectFace f (T.originalPlace i f contained x) = K.projectFace (T.face i) x :=
  (K.projectFaceEquiv f).apply_symm_apply _

end Unfoldings.ConvexCap.ClipSpatialTriangles
