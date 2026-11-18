module

public import Unfoldings.Geometry.NestedSpatialSubdivision
public import Unfoldings.Roof.ConvexRestriction
public import Unfoldings.Roof.SpatialEnvelopeProjection
public import Unfoldings.Development.RigidPlacements

/-! Nested mesh pieces in one old face develop into that exact original metric triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedFaceOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedFaceNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

/-- All fine triangles contained in the specified old projected face. -/
def nestedFaceSet (f : T.Index) : Set U.Index :=
  {i | (U.projectedTriangle i).carrier ⊆ (T.projectedTriangle f).carrier}

open Classical in
def nestedFaceComplex (f : T.Index) := U.pairedComplex.restrictFaces (T.nestedFaceSet U f)

open Classical in
def nestedFacePlace (f : T.Index) (i : T.nestedFaceSet U f) : Plane ≃ᵃⁱ[ℝ] Plane :=
  T.nestedPlace U i.val f i.property

open Classical in
theorem nestedFacePlace_joined (f : T.Index) (s : (T.nestedFaceComplex U f).Seam)
    (x : ((T.nestedFaceComplex U f).triangle ((T.nestedFaceComplex U f).left s).face).Edge
      ((T.nestedFaceComplex U f).left s).edge) :
    T.nestedFacePlace U f ((T.nestedFaceComplex U f).left s).face x.val =
      T.nestedFacePlace U f ((T.nestedFaceComplex U f).right s).face
        ((T.nestedFaceComplex U f).identify s x).val := by
  apply (T.placement f).injective
  change T.placement f (T.nestedCoordinates U _ f x.val) =
    T.placement f (T.nestedCoordinates U _ f ((T.nestedFaceComplex U f).identify s x).val)
  exact (T.nestedCoordinates_spatial U _ f s.property.1 x.val).trans
    ((U.pairedFolding.joined s.val x).trans
      (T.nestedCoordinates_spatial U _ f s.property.2
        ((T.nestedFaceComplex U f).identify s x).val).symm)

open Classical in
theorem nestedFacePlace_triangle_carrier (f : T.Index) (i : T.nestedFaceSet U f) :
    ((T.nestedFaceComplex U f).affineProjectedTriangle
      (fun i => (T.nestedFacePlace U f i).toAffineEquiv) i).carrier =
        (family (T.support f)).project.symm '' (U.projectedTriangle i.val).carrier := by
  have contained : (U.projectedTriangle i.val).carrier ⊆
      (T.projectedTriangle f).carrier := i.property
  let A : Plane →ᵃ[ℝ] Plane := (T.nestedPlace U i.val f contained).toAffineMap
  have injective : Function.Injective A := (T.nestedPlace U i.val f contained).injective
  change ((U.triangle i.val).affineImage A injective).carrier = _
  rw [Triangle.affineImage_carrier]
  change T.nestedPlace U i.val f contained '' (U.triangle i.val).carrier = _
  rw [U.triangle_carrier, Set.image_image]
  congr 1
  funext p
  change (family (T.support f)).project.symm
    ((family (U.support i.val)).project ((family (U.support i.val)).project.symm p)) = _
  rw [AffineEquiv.apply_symm_apply]

open Classical in
/-- Rigid development of one complete old face, keeping all new internal hinges. -/
def nestedFaceDevelopment (f : T.Index) :
    FacewiseDevelopment (T.nestedFaceComplex U f) Set.univ := by
  apply FacewiseDevelopment.ofRigidPlacements _ (T.nestedFacePlace U f)
    (T.nestedFacePlace_joined U f)
  intro i j different
  have ni : i.val ≠ j.val := fun same => different (Subtype.ext same)
  rw [T.nestedFacePlace_triangle_carrier U f i, T.nestedFacePlace_triangle_carrier U f j]
  let H := (family (T.support f)).project.symm.toContinuousAffineEquiv.toHomeomorph
  change Disjoint (interior (H '' _)) (interior (H '' _))
  rw [← H.image_interior, ← H.image_interior]
  exact (Set.disjoint_image_iff H.injective).mpr (U.separated ni)

open Classical in
theorem nestedFaceDevelopment_range (cover : T.FaceRefinement U) (f : T.Index) :
    Set.range (T.nestedFaceDevelopment U f).toPlane = (T.triangle f).carrier := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective (T.nestedFaceComplex U f).Cell
      ((T.nestedFaceComplex U f).glue Set.univ) x
    exact T.nestedCoordinates_inside U i.val f i.property y.property
  · intro member
    have projected : (family (T.support f)).project p ∈ (T.projectedTriangle f).carrier := by
      rw [T.triangle_carrier] at member
      obtain ⟨q, member, rfl⟩ := member
      rwa [AffineEquiv.apply_symm_apply]
    obtain ⟨i, contained, fine⟩ := cover f _ projected
    let y := (family (U.support i)).project.symm ((family (T.support f)).project p)
    have inside : y ∈ (U.triangle i).carrier := by
      rw [U.triangle_carrier]
      exact ⟨_, fine, rfl⟩
    refine ⟨(T.nestedFaceComplex U f).faceMap Set.univ ⟨i, contained⟩ ⟨y, inside⟩, ?_⟩
    change (family (T.support f)).project.symm ((family (U.support i)).project y) = p
    rw [AffineEquiv.apply_symm_apply, AffineEquiv.symm_apply_apply]

variable (conforming : TriangleFamily.Conforming U.projectedTriangle)
  (inside : (interior (clip family W)).Nonempty)

open Classical in
theorem nestedFace_projectedCarrier (cover : T.FaceRefinement U) (f : T.Index) :
    (U.roof conforming inside).restrictedCarrier (T.nestedFaceSet U f) =
      (T.projectedTriangle f).carrier := by
  ext p
  constructor
  · rintro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    rw [U.roof_projectedTriangle] at member
    exact i.property member
  · intro member
    obtain ⟨i, contained, member⟩ := cover f p member
    exact Set.mem_iUnion.mpr ⟨⟨i, contained⟩, by rwa [U.roof_projectedTriangle]⟩

open Classical in
theorem nestedFaceDevelopment_projection (f : T.Index)
    (x : (T.nestedFaceComplex U f).Realization Set.univ) :
    (family (T.support f)).project ((T.nestedFaceDevelopment U f).toPlane x) =
      (U.roof conforming inside).restrictProjection (T.nestedFaceSet U f) x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := MetricGluing.point_surjective (T.nestedFaceComplex U f).Cell
    ((T.nestedFaceComplex U f).glue Set.univ) x
  change (family (T.support f)).project
    ((family (T.support f)).project.symm ((family (U.support i.val)).project y.val)) =
      Cap.horizontal (U.placement i.val y.val)
  rw [AffineEquiv.apply_symm_apply]
  exact ((family (U.support i.val)).horizontal_place y.val).symm

include conforming inside in
open Classical in
/-- Convexity of each complete old face excludes all pinches in its new intrinsic patch. -/
theorem nestedFaceDevelopment_injective (cover : T.FaceRefinement U) (f : T.Index) :
    Function.Injective (T.nestedFaceDevelopment U f).toPlane := by
  have nonempty : (T.nestedFaceSet U f).Nonempty := by
    obtain ⟨i, contained, _⟩ := cover f ((T.projectedTriangle f).vertex 0)
      ((T.projectedTriangle f).vertex_mem 0)
    exact ⟨i, contained⟩
  have injective := (U.roof conforming inside).restrictProjection_injective_of_convex
    (T.nestedFaceSet U f) nonempty (by
      rw [T.nestedFace_projectedCarrier U conforming inside cover f]
      exact (T.projectedTriangle f).convex_carrier)
  intro x y same
  apply injective
  exact (T.nestedFaceDevelopment_projection U conforming inside f x).symm.trans
    ((congrArg (fun p => (family (T.support f)).project p) same).trans
      (T.nestedFaceDevelopment_projection U conforming inside f y))

end Unfoldings.SpatialEnvelope.Triangulation
