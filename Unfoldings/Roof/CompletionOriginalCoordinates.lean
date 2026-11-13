module

public import Unfoldings.Roof.CompletionOriginalPieces
public import Unfoldings.Geometry.AffineEnd

/-! Auxiliary pieces inside old roof faces retain their original Euclidean metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

/-- Completed graph points over old faces are precisely the original spatial points. -/
theorem point_eq_original_place (f : Face) (x : C.Cell f) :
    SpatialEnvelope.point (K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (K.projectFace f x.val) = K.folding.place f x.val := by
  have in_domain : K.projectFace f x.val ∈ K.footprint := by
    apply K.projectedTriangle_subset_footprint f
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier]
    exact ⟨x.val, x.property, rfl⟩
  ext i
  fin_cases i
  · rfl
  · rfl
  · change SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (K.projectFace f x.val) = K.folding.place f x.val 2
    rw [E.unchanged _ in_domain, K.roofHeight_face]

/-- Auxiliary local coordinates pulled back to the whole original face. -/
def originalCoordinates (i : E.partition.Index) (f : Face) : Plane ≃ᵃ[ℝ] Plane :=
  ((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i)).project.trans
    (K.projectFaceEquiv f).symm

/-- Contained fine triangles lie on exactly the original rigid supporting plane, everywhere. -/
theorem originalCoordinates_spatial (i : E.partition.Index) (f : Face)
    (contained : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier)
    (x : Plane) : K.folding.place f (E.originalCoordinates i f x) = E.partition.placement i x := by
  have on_face {x : Plane} (member : x ∈ (E.partition.triangle i).carrier) :
      K.folding.place f (E.originalCoordinates i f x) = E.partition.placement i x := by
    have projected := E.partition.projected_member i member
    have old := contained projected
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier] at old
    obtain ⟨y, inside, same⟩ := old
    have coordinates : E.originalCoordinates i f x = y := by
      change (K.projectFaceEquiv f).symm
        (((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i)).project x) = y
      rw [← same]
      exact (K.projectFaceEquiv f).symm_apply_apply y
    rw [coordinates, ← E.point_eq_original_place f ⟨y, inside⟩, same]
    exact (E.partition.placement_eq_point i member).symm
  have maps : (K.folding.place f).toAffineMap.comp (E.originalCoordinates i f).toAffineMap =
      (E.partition.placement i).toAffineMap := by
    apply (E.partition.triangle i).affine_ext
    intro j
    exact on_face ((E.partition.triangle i).vertex_mem j)
  exact congrArg (fun A : Plane →ᵃ[ℝ] Space => A x) maps

theorem originalCoordinates_isometry (i : E.partition.Index) (f : Face)
    (contained : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) :
    Isometry (E.originalCoordinates i f) := by
  intro x y
  calc
    edist (E.originalCoordinates i f x) (E.originalCoordinates i f y) =
        edist (K.folding.place f (E.originalCoordinates i f x))
          (K.folding.place f (E.originalCoordinates i f y)) :=
      ((K.folding.place f).isometry.edist_eq _ _).symm
    _ = edist (E.partition.placement i x) (E.partition.placement i y) := by
      rw [E.originalCoordinates_spatial i f contained x,
        E.originalCoordinates_spatial i f contained y]
    _ = edist x y := (E.partition.placement i).isometry.edist_eq x y

/-- The actual original-face coordinate map is an affine isometry. -/
def originalPlace (i : E.partition.Index) (f : Face)
    (contained : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  let A := (E.originalCoordinates_isometry i f contained).affineIsometryOfStrictConvexSpace
  { AffineEquiv.ofBijective (φ := A.toAffineMap)
      ⟨A.injective, (E.originalCoordinates i f).surjective⟩ with norm_map := A.norm_map }

@[simp] theorem originalPlace_apply (i : E.partition.Index) (f : Face)
    (contained : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier)
    (x : Plane) : E.originalPlace i f contained x = E.originalCoordinates i f x := rfl

theorem originalPlace_projection (i : E.partition.Index) (f : Face)
    (contained : (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier)
    (x : Plane) : K.projectFace f (E.originalPlace i f contained x) =
      ((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i)).project x :=
  (K.projectFaceEquiv f).apply_symm_apply _

end Unfoldings.ConvexRoof.CompletionMesh
