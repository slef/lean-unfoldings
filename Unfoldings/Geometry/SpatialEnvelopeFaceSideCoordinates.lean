module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSide
public import Unfoldings.Geometry.SpatialPlaneCoordinates

/-! One-sided support cells have common rigid coordinates with their exact region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- All selected actual pieces expressed in the anchor support's original rigid coordinates. -/
def faceSideCell (anchor : A) (signs : A → Bool) (a : P.FaceSideIndex anchor signs) : Set Plane :=
  (family (P.support anchor)).project.symm '' P.footprint a.val

/-- Coplanar physical pieces retain their exact Euclidean metric in the common coordinates. -/
def faceSideCellIsometryEquiv (anchor : A) (signs : A → Bool) (a : P.FaceSideIndex anchor signs) :
    P.planarCell a.val ≃ᵢ P.faceSideCell anchor signs a := by
  let changeFrame := (family (P.support a.val)).coordinateEquiv
    (family (P.support anchor)) a.property.1
  let map (x : P.planarCell a.val) : P.faceSideCell anchor signs a :=
    ⟨changeFrame x.val, by
      obtain ⟨p, hp, equal⟩ := x.property
      change (family (P.support anchor)).project.symm
        ((family (P.support a.val)).project x.val) ∈ _
      rw [← equal, (family (P.support a.val)).project.apply_symm_apply]
      exact ⟨p, hp, rfl⟩⟩
  refine ⟨Equiv.ofBijective map ⟨?_, ?_⟩, ?_⟩
  · intro x y equal
    exact Subtype.ext (changeFrame.injective (congrArg Subtype.val equal))
  · rintro ⟨y, p, hp, rfl⟩
    refine ⟨⟨(family (P.support a.val)).project.symm p, p, hp, rfl⟩, ?_⟩
    apply Subtype.ext
    change (family (P.support anchor)).project.symm
      ((family (P.support a.val)).project ((family (P.support a.val)).project.symm p)) = _
    rw [(family (P.support a.val)).project.apply_symm_apply]
  · intro x y
    exact changeFrame.isometry x.val y.val

omit [Finite A] in
theorem place_faceSideCellIsometryEquiv (anchor : A) (signs : A → Bool)
    (a : P.FaceSideIndex anchor signs) (x : P.planarCell a.val) :
    (family (P.support anchor)).place (P.faceSideCellIsometryEquiv anchor signs a x).val =
      (family (P.support a.val)).place x.val :=
  (family (P.support a.val)).place_coordinateEquiv (family (P.support anchor)) a.property.1 x.val

omit [Finite A] in
theorem isClosed_faceSideCell (anchor : A) (signs : A → Bool) (a : P.FaceSideIndex anchor signs) :
    IsClosed (P.faceSideCell anchor signs a) :=
  (family (P.support anchor)).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _
    (P.closed a.val)

omit [Finite A] in
theorem convex_faceSideCell (anchor : A) (signs : A → Bool) (a : P.FaceSideIndex anchor signs) :
    Convex ℝ (P.faceSideCell anchor signs a) :=
  (P.convex a.val).affine_image (family (P.support anchor)).project.symm.toAffineMap

omit [Finite A] in
theorem faceSideCell_interior_nonempty (anchor : A) (signs : A → Bool)
    (a : P.FaceSideIndex anchor signs) : (interior (P.faceSideCell anchor signs a)).Nonempty := by
  change (interior ((family (P.support anchor)).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    P.footprint a.val)).Nonempty
  rw [← Homeomorph.image_interior]
  exact (P.full a.val).image _

/-- The actual common-coordinate cells cover precisely the complete convex support-side region. -/
theorem iUnion_faceSideCell (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x) :
    (⋃ a : P.FaceSideIndex anchor signs, P.faceSideCell anchor signs a) =
      (family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs := by
  rw [P.faceSideRegion_eq_iUnion anchor f proper signs aligned, Set.image_iUnion]
  rfl

end Unfoldings.SpatialEnvelope.WholePartition
