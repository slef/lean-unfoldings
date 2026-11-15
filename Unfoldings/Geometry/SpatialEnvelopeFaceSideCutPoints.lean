module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCut

/-! Exact original cell copies and spatial points under the one-sided face-cut embedding. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

@[simp] theorem cutIsometryEquiv_of (cuts : Set Plane) (a : A) (x : P.planarCell a) :
    P.cutIsometryEquiv cuts
      (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a x) =
      MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a
        (P.cellIsometryEquiv a x) := rfl

/-- Each common-coordinate point maps to its original actual rigid-cell copy. -/
@[simp] theorem faceSideCutMap_of (anchor : A) (signs : A → Bool) (cuts : Set Plane)
    (a : P.FaceSideIndex anchor signs) (x : P.faceSideCell anchor signs a) :
    P.faceSideCutMap anchor signs cuts
      (MetricGluing.of (fun a => P.faceSideCell anchor signs a)
        (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
          ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation a x) =
      MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a.val
        ((P.faceSideCellIsometryEquiv anchor signs a).symm x) := by
  apply (P.cutIsometryEquiv cuts).injective
  change (P.cutIsometryEquiv cuts) ((P.cutIsometryEquiv cuts).symm _) = _
  rw [IsometryEquiv.apply_symm_apply, MetricGluing.cutIsometricCoverMap_of,
    P.cutIsometryEquiv_of]
  apply congrArg (MetricGluing.of (fun a => P.spatialCell a) (P.cutPhysicalSeams cuts).relation a.val)
  apply Subtype.ext
  have placed := P.place_faceSideCellIsometryEquiv anchor signs a
    ((P.faceSideCellIsometryEquiv anchor signs a).symm x)
  rw [IsometryEquiv.apply_symm_apply] at placed
  exact placed

/-- The complete face-side cut embedding retains every original spatial point. -/
theorem restoreCut_faceSideCutMap (anchor : A) (signs : A → Bool) (cuts : Set Plane)
    (x : P.FaceSideCut anchor signs cuts) :
    (P.restoreCut cuts (P.faceSideCutMap anchor signs cuts x)).val =
      (family (P.support anchor)).place
        ((MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
          ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).fold x) := by
  obtain ⟨⟨a, p⟩, rfl⟩ := MetricGluing.point_surjective (fun a => P.faceSideCell anchor signs a)
    (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation x
  change (P.restoreCut cuts (P.faceSideCutMap anchor signs cuts
    (MetricGluing.of (fun a => P.faceSideCell anchor signs a)
      (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
        ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation a p))).val =
      (family (P.support anchor)).place p.val
  rw [P.faceSideCutMap_of, P.restoreCut_of]
  have placed := P.place_faceSideCellIsometryEquiv anchor signs a
    ((P.faceSideCellIsometryEquiv anchor signs a).symm p)
  rw [IsometryEquiv.apply_symm_apply] at placed
  exact placed.symm

/-- The convex-region coordinate is the original physical planar coordinate. -/
theorem faceSideCutIsometryEquiv_val (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)
    (x : P.FaceSideCut anchor signs cuts) :
    (P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level x).val =
      (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
        ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).fold x := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective (fun a => P.faceSideCell anchor signs a)
    (MetricGluing.cutSeams (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))).relation x
  rfl

/-- Embed the entire physical convex face-side region in the same original whole-roof cut. -/
def faceSideRegionMap (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0) :
    PolygonalPoint ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs) →
      P.Cut cuts :=
  P.faceSideCutMap anchor signs cuts ∘
    (P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level).symm

theorem faceSideRegionMap_isometry (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0) :
    Isometry (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level) :=
  (P.faceSideCutMap_isometry anchor f proper signs aligned cuts cut_closed cut_level).comp
    (P.faceSideCutIsometryEquiv anchor f proper signs aligned cuts cut_closed cut_level).symm.isometry

/-- The entire region embedding folds to its original spatial support plane. -/
theorem restoreCut_faceSideRegionMap (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)
    (x : PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs)) :
    (P.restoreCut cuts
      (P.faceSideRegionMap anchor f proper signs aligned cuts cut_closed cut_level x)).val =
        (family (P.support anchor)).place x.val := by
  rw [faceSideRegionMap, Function.comp_apply, P.restoreCut_faceSideCutMap,
    ← P.faceSideCutIsometryEquiv_val anchor f proper signs aligned cuts cut_closed cut_level,
    IsometryEquiv.apply_symm_apply]

end Unfoldings.SpatialEnvelope.WholePartition
