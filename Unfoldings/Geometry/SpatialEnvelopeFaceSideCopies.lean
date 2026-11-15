module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall

/-! Canonical full face-side banks retain their original side-labeled metric copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]
  (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0) (signs : A → Bool)
  (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
  (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)

/-- Every canonical full-region bank point is one of its original selected physical cell copies. -/
theorem faceSideRegionMap_has_spatial_copy (anchor : A)
    (source : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs)) :
    ∃ a : P.FaceSideIndex anchor signs, ∃ y : P.spatialCell a.val,
      P.cutIsometryEquiv cuts
        (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level source) =
          MetricGluing.of (fun a => P.spatialCell a)
            (P.cutPhysicalSeams cuts).relation a.val y := by
  let C := P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level
  obtain ⟨⟨a, x⟩, represents⟩ := MetricGluing.point_surjective
    (fun a => P.faceSideCell anchor signs a)
    (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation (C.symm source)
  let y := P.cellIsometryEquiv a.val ((P.faceSideCellIsometryEquiv anchor signs a).symm x)
  refine ⟨a, y, ?_⟩
  exact (congrArg (fun c => P.cutIsometryEquiv cuts (P.faceSideCutMap anchor signs cuts c))
    represents.symm).trans
      ((congrArg (P.cutIsometryEquiv cuts) (P.faceSideCutMap_of anchor signs cuts a x)).trans
        (P.cutIsometryEquiv_of cuts a.val _))

/-- The two canonical full face-side regions remain distinct along a local complete cut line. -/
theorem faceSideRegionMap_ne_of_opposite_sign (l b : A)
    (left : PolygonalPoint ((family (P.support l)).project.symm '' P.faceSideRegion l f signs))
    (right : PolygonalPoint ((family (P.support b)).project.symm '' P.faceSideRegion b f signs))
    {U : Set Plane} (open_U : IsOpen U) (cut_line : ∀ z ∈ U, f z = 0 → z ∈ cuts)
    (inside : Cap.horizontal (P.restoreCut cuts
      (P.faceSideRegionMap l f proper signs aligned cuts cut_closed cut_level left)).val ∈ U)
    (different : signs l ≠ signs b) :
    P.faceSideRegionMap l f proper signs aligned cuts cut_closed cut_level left ≠
      P.faceSideRegionMap b f proper signs aligned cuts cut_closed cut_level right := by
  obtain ⟨a, x, first⟩ := P.faceSideRegionMap_has_spatial_copy f proper signs aligned
    cuts cut_closed cut_level l left
  obtain ⟨c, y, last⟩ := P.faceSideRegionMap_has_spatial_copy f proper signs aligned
    cuts cut_closed cut_level b right
  intro equal
  have related := (P.cutPhysicalSeams cuts).exact ⟨a.val, x⟩ ⟨c.val, y⟩
    (first.symm.trans ((congrArg (P.cutIsometryEquiv cuts) equal).trans last))
  have physical : x.val = (P.restoreCut cuts
      (P.faceSideRegionMap l f proper signs aligned cuts cut_closed cut_level left)).val :=
    (congrArg (P.cutPhysicalSeams cuts).fold first).symm.trans (P.fold_cutIsometryEquiv cuts _)
  have on_side := P.cutClass_side_eq cuts f signs aligned open_U cut_line
    (physical.symm ▸ inside) related
  exact different (a.property.2.symm.trans (on_side.trans c.property.2))

end Unfoldings.SpatialEnvelope.WholePartition
