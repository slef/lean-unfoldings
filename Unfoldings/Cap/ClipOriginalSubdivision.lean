module

public import Unfoldings.Cap.ClipOriginalPieces
public import Unfoldings.Cap.ClipPairings
public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Complex.Subdivision

/-! Restrict the actual roof mesh to an isometric subdivision of the original input faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalClipIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
def originalComplex := L.partition.pairedComplex.restrictFaces L.originalPieceSet

open Classical in
def originalSubdivision (lower : Z < 0) : C.Subdivision L.originalComplex where
  parent := L.originalParent
  place i := L.partition.originalPlace i.val (L.originalParent i) (L.originalParent_contains i)
  inside i x member := by
    have projected : K.projectFace (L.partition.face i.val) x ∈
        (L.partition.projectedTriangle i.val).carrier := by
      change x ∈ (L.partition.triangle i.val).carrier at member
      rw [L.partition.triangle_carrier] at member
      obtain ⟨p, member, rfl⟩ := member
      simpa only [show K.projectFace (L.partition.face i.val) =
        (K.projectFaceEquiv (L.partition.face i.val)).toAffineMap from rfl,
        AffineEquiv.coe_toAffineMap, AffineEquiv.apply_symm_apply] using member
    have old := L.originalParent_contains i projected
    rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier] at old
    obtain ⟨y, inside, same⟩ := old
    have coordinates : L.partition.originalPlace i.val (L.originalParent i)
        (L.originalParent_contains i) x = y := by
      rw [L.partition.originalPlace_apply]
      change (K.projectFaceEquiv (L.originalParent i)).symm
        (K.projectFace (L.partition.face i.val) x) = y
      rw [← same]
      exact (K.projectFaceEquiv (L.originalParent i)).symm_apply_apply y
    exact coordinates.symm ▸ inside
  cover f x := by
    let p := K.projectFace f x.val
    have projected : p ∈ (K.projectedTriangle f).carrier := by
      rw [ConvexCap.projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨x.val, x.property, rfl⟩
    obtain ⟨i, parent, member⟩ := L.original_piece_cover lower f p projected
    let y := (K.projectFaceEquiv (L.partition.face i.val)).symm p
    have fine : y ∈ (L.partition.triangle i.val).carrier := by
      rw [L.partition.triangle_carrier]
      exact ⟨p, member, rfl⟩
    refine ⟨i, ⟨y, fine⟩, parent, ?_⟩
    rw [L.partition.originalPlace_apply]
    change (K.projectFaceEquiv (L.originalParent i)).symm
      ((K.projectFaceEquiv (L.partition.face i.val))
        ((K.projectFaceEquiv (L.partition.face i.val)).symm p)) = x.val
    rw [AffineEquiv.apply_symm_apply, parent]
    exact (K.projectFaceEquiv f).symm_apply_apply x.val

end Unfoldings.ConvexCap.LineAlignedClip
