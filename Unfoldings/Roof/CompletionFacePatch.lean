module

public import Unfoldings.Roof.CompletionOriginalCoordinates
public import Unfoldings.Roof.ConvexRestriction
public import Unfoldings.Roof.SpatialEnvelopeProjection
public import Unfoldings.Development.RigidPlacements

/-! Actual completion pieces in one original face develop into precisely that original triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations) (f : Face)

local instance completionFacePatchIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

/-- All and only physical triangles wholly contained in this original face. -/
def facePieceSet : Set E.partition.Index :=
  {i | (E.partition.projectedTriangle i).carrier ⊆ (K.projectedTriangle f).carrier}

open Classical in
def facePieceComplex := E.partition.pairedComplex.restrictFaces (E.facePieceSet f)

open Classical in
def facePiecePlace (i : E.facePieceSet f) : Plane ≃ᵃⁱ[ℝ] Plane :=
  E.originalPlace i.val f i.property

open Classical in
theorem facePiece_projectedCarrier :
    (E.partition.roof E.conforming E.interior_nonempty).restrictedCarrier (E.facePieceSet f) =
      (K.projectedTriangle f).carrier := by
  ext p
  constructor
  · rintro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    rw [E.partition.roof_projectedTriangle] at member
    exact i.property member
  · intro member
    obtain ⟨i, contained, member⟩ := E.original_face_covered_by_contained_pieces f p member
    exact Set.mem_iUnion.mpr ⟨⟨i, contained⟩, by rwa [E.partition.roof_projectedTriangle]⟩

open Classical in
theorem facePiecePlace_joined (s : (E.facePieceComplex f).Seam)
    (x : ((E.facePieceComplex f).triangle ((E.facePieceComplex f).left s).face).Edge
      ((E.facePieceComplex f).left s).edge) :
    E.facePiecePlace f ((E.facePieceComplex f).left s).face x.val =
      E.facePiecePlace f ((E.facePieceComplex f).right s).face
        ((E.facePieceComplex f).identify s x).val := by
  apply (K.folding.place f).injective
  change K.folding.place f (E.originalCoordinates _ f x.val) =
    K.folding.place f (E.originalCoordinates _ f ((E.facePieceComplex f).identify s x).val)
  exact (E.originalCoordinates_spatial _ f s.property.1 x.val).trans
    ((E.partition.pairedFolding.joined s.val x).trans
      (E.originalCoordinates_spatial _ f s.property.2
        ((E.facePieceComplex f).identify s x).val).symm)

open Classical in
theorem facePiecePlace_triangle_carrier (i : E.facePieceSet f) :
    ((E.facePieceComplex f).affineProjectedTriangle
      (fun i => (E.facePiecePlace f i).toAffineEquiv) i).carrier =
        (K.projectFaceEquiv f).symm '' (E.partition.projectedTriangle i.val).carrier := by
  have contained : (E.partition.projectedTriangle i.val).carrier ⊆
      (K.projectedTriangle f).carrier := i.property
  let A : Plane →ᵃ[ℝ] Plane := (E.originalPlace i.val f contained).toAffineMap
  have injective : Function.Injective A := (E.originalPlace i.val f contained).injective
  change ((E.partition.triangle i.val).affineImage A injective).carrier = _
  rw [Triangle.affineImage_carrier]
  change E.originalPlace i.val f contained '' (E.partition.triangle i.val).carrier = _
  rw [E.partition.triangle_carrier, Set.image_image]
  congr 1
  funext p
  rw [E.originalPlace_apply]
  change (K.projectFaceEquiv f).symm
    (((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i.val)).project
      (((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i.val)).project.symm
        p)) = _
  rw [AffineEquiv.apply_symm_apply]

open Classical in
/-- The physical face pieces have their inherited original rigid coordinates and actual hinges. -/
def facePieceDevelopment : FacewiseDevelopment (E.facePieceComplex f) Set.univ := by
  apply FacewiseDevelopment.ofRigidPlacements _ (E.facePiecePlace f) (E.facePiecePlace_joined f)
  intro i j different
  have ni : i.val ≠ j.val := fun same => different (Subtype.ext same)
  rw [E.facePiecePlace_triangle_carrier f i, E.facePiecePlace_triangle_carrier f j]
  change Disjoint (interior ((K.projectFaceHomeomorph f).symm '' _))
    (interior ((K.projectFaceHomeomorph f).symm '' _))
  rw [← (K.projectFaceHomeomorph f).symm.image_interior,
    ← (K.projectFaceHomeomorph f).symm.image_interior]
  exact (Set.disjoint_image_iff (K.projectFaceHomeomorph f).symm.injective).mpr
    (E.partition.separated ni)

open Classical in
theorem facePieceDevelopment_projection (x : (E.facePieceComplex f).Realization Set.univ) :
    K.projectFace f ((E.facePieceDevelopment f).toPlane x) =
      (E.partition.roof E.conforming E.interior_nonempty).restrictProjection
        (E.facePieceSet f) x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective (E.facePieceComplex f).Cell
    ((E.facePieceComplex f).glue Set.univ) x
  change K.projectFace f (E.originalPlace i.val f i.property y.val) =
    Cap.horizontal (E.partition.placement i.val y.val)
  exact (E.originalPlace_projection i.val f i.property y.val).trans
    (((K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (E.partition.support i.val)).horizontal_place y.val).symm

open Classical in
theorem facePieceDevelopment_injective : Function.Injective (E.facePieceDevelopment f).toPlane := by
  have nonempty : (E.facePieceSet f).Nonempty := by
    obtain ⟨i, contained, _⟩ := E.original_face_covered_by_contained_pieces f
      ((K.projectedTriangle f).vertex 0) ((K.projectedTriangle f).vertex_mem 0)
    exact ⟨i, contained⟩
  have injective := (E.partition.roof E.conforming E.interior_nonempty)
    |>.restrictProjection_injective_of_convex (E.facePieceSet f) nonempty (by
      rw [E.facePiece_projectedCarrier f]
      exact (K.projectedTriangle f).convex_carrier)
  intro x y same
  apply injective
  exact (E.facePieceDevelopment_projection f x).symm.trans
    ((congrArg (K.projectFace f) same).trans (E.facePieceDevelopment_projection f y))

open Classical in
/-- The original metric triangle, rather than only its horizontal projection, is covered exactly. -/
theorem facePieceDevelopment_range :
    Set.range (E.facePieceDevelopment f).toPlane = (C.triangle f).carrier := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective (E.facePieceComplex f).Cell
      ((E.facePieceComplex f).glue Set.univ) x
    have projected := i.property (E.partition.projected_member i.val y.property)
    rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier] at projected
    obtain ⟨z, member, equal⟩ := projected
    have same : E.facePiecePlace f i y.val = z := by
      change (K.projectFaceEquiv f).symm
        (((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i.val)).project
          y.val) = z
      rw [← equal]
      exact (K.projectFaceEquiv f).symm_apply_apply z
    change E.facePiecePlace f i y.val ∈ (C.triangle f).carrier
    exact same.symm ▸ member
  · intro member
    let z := K.projectFace f p
    have projected : z ∈ (K.projectedTriangle f).carrier := by
      rw [ConvexRoof.projectedTriangle, Triangle.affineImage_carrier]
      exact ⟨p, member, rfl⟩
    obtain ⟨i, contained, fine⟩ := E.original_face_covered_by_contained_pieces f z projected
    let y := ((K.completionPlanes E.tentHeight (Real.sin φ / 2))
      (E.partition.support i)).project.symm z
    have inside : y ∈ (E.partition.triangle i).carrier := by
      rw [E.partition.triangle_carrier]
      exact ⟨z, fine, rfl⟩
    refine ⟨(E.facePieceComplex f).faceMap Set.univ ⟨i, contained⟩ ⟨y, inside⟩, ?_⟩
    change E.originalPlace i f contained y = p
    rw [E.originalPlace_apply]
    change (K.projectFaceEquiv f).symm
      (((K.completionPlanes E.tentHeight (Real.sin φ / 2)) (E.partition.support i)).project y) = p
    rw [AffineEquiv.apply_symm_apply]
    exact (K.projectFaceEquiv f).symm_apply_apply p

end Unfoldings.ConvexRoof.CompletionMesh
