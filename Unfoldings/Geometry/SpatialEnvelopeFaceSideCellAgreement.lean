module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCopies

/-! Full face-side region embeddings agree with every specified original cell copy. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]
  (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0) (signs : A → Bool)
  (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
  (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)

/-- A specified selected original cell copy is exactly the canonical bank copy at that point. -/
theorem faceSideRegionMap_eq_of_spatial_copy (a : P.FaceSideIndex anchor signs)
    (y : P.spatialCell a.val)
    (source : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs))
    (position : y.val = (family (P.support anchor)).place source.val) :
    P.cutIsometryEquiv cuts
      (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source) =
        MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a.val y := by
  obtain ⟨z, represents⟩ := P.faceSideRegionMap_covers_spatial_cell anchor f proper signs aligned
    cuts cut_closed cut_level a y
  have physical : (family (P.support anchor)).place z.val = y.val :=
    (P.restoreCut_faceSideRegionMap anchor f proper signs aligned
      cuts cut_closed cut_level z).symm.trans
      ((P.fold_cutIsometryEquiv cuts _).symm.trans
        (congrArg (P.cutPhysicalSeams cuts).fold represents))
  have equal : z = source := PolygonalPoint.ext
    ((family (P.support anchor)).place.injective (physical.trans position))
  exact (congrArg (fun w => P.cutIsometryEquiv cuts
    (P.faceSideRegionMap anchor f proper signs aligned
      cuts cut_closed cut_level w)) equal).symm.trans
      represents

/-- Canonical whole bank points agree with the actual anchor cell lift wherever it is present. -/
theorem faceSideRegionMap_eq_liftCell (p : P.footprint anchor)
    (source : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs))
    (coordinate : source.val = (family (P.support anchor)).project.symm p.val) :
    P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source =
      P.liftCell cuts anchor p := by
  let a : P.FaceSideIndex anchor signs := ⟨anchor, rfl, rfl⟩
  let y := P.cellIsometryEquiv anchor
    ⟨(family (P.support anchor)).project.symm p.val, p.val, p.property, rfl⟩
  apply (P.cutIsometryEquiv cuts).injective
  exact P.faceSideRegionMap_eq_of_spatial_copy anchor f proper signs aligned
    cuts cut_closed cut_level
    a y source (congrArg (family (P.support anchor)).place coordinate).symm

end Unfoldings.SpatialEnvelope.WholePartition
