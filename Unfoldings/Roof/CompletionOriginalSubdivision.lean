module

public import Unfoldings.Roof.CompletionOriginalCoordinates
public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Complex.Subdivision

/-! The actual auxiliary completion restricts to an isometric subdivision of every original face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance : Fintype E.partition.Index := @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The actual auxiliary complex restricted to pieces of whole original faces. -/
def originalComplex := E.partition.pairedComplex.restrictFaces E.originalPieceSet

open Classical in
/-- Each whole original face is exactly covered by its isometric physical auxiliary pieces. -/
def originalSubdivision : C.Subdivision E.originalComplex where
  parent := E.originalParent
  place i := E.originalPlace i.val (E.originalParent i) (E.originalParent_contains i)
  inside i x member := by
    have projected := E.partition.projected_member i.val member
    have old := E.originalParent_contains i projected
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier] at old
    obtain ⟨y, inside, same⟩ := old
    have coordinates : E.originalPlace i.val (E.originalParent i)
        (E.originalParent_contains i) x = y := by
      rw [E.originalPlace_apply]
      change (K.projectFaceEquiv (E.originalParent i)).symm
        (((K.completionPlanes E.tentHeight (Real.sin φ / 2))
          (E.partition.support i.val)).project x) = y
      rw [← same]
      exact (K.projectFaceEquiv (E.originalParent i)).symm_apply_apply y
    exact coordinates.symm ▸ inside
  cover f x := by
    let p := K.projectFace f x.val
    have projected : p ∈ (K.projectedTriangle f).carrier := by
      rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨x.val, x.property, rfl⟩
    obtain ⟨i, parent, member⟩ := E.original_piece_cover f p projected
    let family := K.completionPlanes E.tentHeight (Real.sin φ / 2)
    let P := (family (E.partition.support i.val)).project
    let y := P.symm p
    have fine : y ∈ (E.partition.triangle i.val).carrier := by
      rw [E.partition.triangle_carrier]
      exact ⟨p, member, rfl⟩
    refine ⟨i, ⟨y, fine⟩, parent, ?_⟩
    rw [E.originalPlace_apply]
    change (K.projectFaceEquiv (E.originalParent i)).symm (P (P.symm p)) = x.val
    rw [P.apply_symm_apply, parent]
    exact (K.projectFaceEquiv f).symm_apply_apply x.val

end Unfoldings.ConvexRoof.CompletionMesh
