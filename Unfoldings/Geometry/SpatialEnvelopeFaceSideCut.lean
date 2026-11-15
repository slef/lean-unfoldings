module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCoordinates
public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Metric.CutIsometricCoverMap

/-! Complete original one-sided physical face regions embed isometrically in the full roof cut. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The entire one-sided actual face cut, expressed in its original support's rigid coordinates. -/
abbrev FaceSideCut (anchor : A) (signs : A → Bool) (cuts : Set Plane) :=
  MetricGluing.PolygonalCut (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs)
    ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))

omit [Finite A] in
/-- The common-coordinate piece still occupies precisely its own original physical cell. -/
theorem faceSideCell_place_subset (anchor : A) (signs : A → Bool)
    (a : P.FaceSideIndex anchor signs) :
    (family (P.support anchor)).place '' P.faceSideCell anchor signs a ⊆ P.spatialCell a.val := by
  rintro z ⟨x, hx, rfl⟩
  let B := P.faceSideCellIsometryEquiv anchor signs a
  let y := B.symm ⟨x, hx⟩
  have physical := P.place_faceSideCellIsometryEquiv anchor signs a y
  change (family (P.support anchor)).place (B (B.symm ⟨x, hx⟩)).val =
    (family (P.support a.val)).place y.val at physical
  rw [B.apply_symm_apply] at physical
  exact ⟨y.val, y.property, physical.symm⟩

/-- Include the whole physical face-side cut into the actual cut of this same roof. -/
def faceSideCutMap (anchor : A) (signs : A → Bool) (cuts : Set Plane) :
    P.FaceSideCut anchor signs cuts → P.Cut cuts :=
  (P.cutIsometryEquiv cuts).symm ∘
    MetricGluing.cutIsometricCoverMap (P.faceSideCell anchor signs)
      (P.isClosed_faceSideCell anchor signs) (family (P.support anchor)).place
      (family (P.support anchor)).place.isometry P.spatialCell P.isClosed_spatialCell Subtype.val
      (P.faceSideCell_place_subset anchor signs) (Cap.horizontal ⁻¹' cuts)

omit [Finite A] in
/-- Line-supported cuts avoid the interior of the common-coordinate face-side region. -/
theorem faceSideCut_disjoint_interior (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool) (cuts : Set Plane) (cut_level : ∀ x ∈ cuts, f x = 0) :
    Disjoint (interior ((family (P.support anchor)).project.symm ''
      P.faceSideRegion anchor f signs))
      ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts)) := by
  let Q := family (P.support anchor)
  let region := Q.project.symm '' P.faceSideRegion anchor f signs
  let height := (AffineArrangement.signed f (signs anchor)).comp Q.project.toAffineMap
  have signed_proper : AffineArrangement.signed f (signs anchor) ≠ 0 := by
    cases value : signs anchor <;> simpa only [AffineArrangement.signed, value,
      Bool.false_eq_true, ↓reduceIte, neg_ne_zero] using proper
  have height_proper : height ≠ 0 := by
    intro zero
    apply signed_proper
    ext x
    have equal := congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h (Q.project.symm x)) zero
    change AffineArrangement.signed f (signs anchor) (Q.project (Q.project.symm x)) = 0 at equal
    rwa [Q.project.apply_symm_apply] at equal
  have lower : ∀ x ∈ region, 0 ≤ height x := by
    rintro x ⟨p, hp, rfl⟩
    change 0 ≤ AffineArrangement.signed f (signs anchor) (Q.project (Q.project.symm p))
    rw [Q.project.apply_symm_apply]
    exact hp.2
  have outside : Disjoint (interior region) (Q.place ⁻¹' (Cap.horizontal ⁻¹' cuts)) := by
    apply Set.disjoint_left.mpr
    intro x inside on_cut
    have zero := cut_level _ on_cut
    rw [Q.horizontal_place] at zero
    have height_zero : height x = 0 := by
      change AffineArrangement.signed f (signs anchor) (Q.project x) = 0
      simp only [AffineArrangement.signed_apply, zero, neg_zero, ite_self]
    exact not_mem_interior_of_affine_lower_bound height height_proper lower height_zero inside
  exact outside

/-- The complete one-sided original face cut has exactly its physical convex-region metric. -/
def faceSideCutIsometryEquiv (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0) :
    P.FaceSideCut anchor signs cuts ≃ᵢ PolygonalPoint
      ((family (P.support anchor)).project.symm '' P.faceSideRegion anchor f signs) :=
  MetricGluing.boundaryCutIsometryEquiv (P.faceSideCell anchor signs)
    (P.isClosed_faceSideCell anchor signs)
    ((family (P.support anchor)).place ⁻¹' (Cap.horizontal ⁻¹' cuts))
    (P.convex_faceSideCell anchor signs) (P.faceSideCell_interior_nonempty anchor signs)
    (P.iUnion_faceSideCell anchor f proper signs aligned).symm
    ((P.convex_faceSideRegion anchor f signs).affine_image
      (family (P.support anchor)).project.symm.toAffineMap)
    (cut_closed.preimage (Cap.horizontalCLM.continuous.comp
      (family (P.support anchor)).place.continuous))
    (P.faceSideCut_disjoint_interior anchor f proper signs cuts cut_level)

/-- Cuts confined to the aligned line leave the exact complete one-sided metric in the full roof.
Original cells, physical placement and intrinsic distances are all constructed, not assumed. -/
theorem faceSideCutMap_isometry (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (cuts : Set Plane) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0) :
    Isometry (P.faceSideCutMap anchor signs cuts) := by
  let Q := family (P.support anchor)
  let region := Q.project.symm '' P.faceSideRegion anchor f signs
  have cover : region = ⋃ a : P.FaceSideIndex anchor signs, P.faceSideCell anchor signs a :=
    (P.iUnion_faceSideCell anchor f proper signs aligned).symm
  have convex_region : Convex ℝ region :=
    (P.convex_faceSideRegion anchor f signs).affine_image Q.project.symm.toAffineMap
  have closed_cut : IsClosed (Q.place ⁻¹' (Cap.horizontal ⁻¹' cuts)) :=
    cut_closed.preimage (Cap.horizontalCLM.continuous.comp Q.place.continuous)
  have outside := P.faceSideCut_disjoint_interior anchor f proper signs cuts cut_level
  have source_isometry := MetricGluing.cut_fold_isometry_of_boundary_cuts
    (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs) Q.place
    (Cap.horizontal ⁻¹' cuts) (P.convex_faceSideCell anchor signs)
    (P.faceSideCell_interior_nonempty anchor signs) cover convex_region closed_cut outside
  have physical_isometry := MetricGluing.cutIsometricCoverMap_isometry
    (P.faceSideCell anchor signs) (P.isClosed_faceSideCell anchor signs) Q.place Q.place.isometry
    P.spatialCell P.isClosed_spatialCell Subtype.val (P.faceSideCell_place_subset anchor signs)
    (Cap.horizontal ⁻¹' cuts) source_isometry
  exact (P.cutIsometryEquiv cuts).symm.isometry.comp physical_isometry

end Unfoldings.SpatialEnvelope.WholePartition
