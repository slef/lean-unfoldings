module

public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Metric.FlatPhysicalCutRefinement

/-! Actual whole-roof partition refinements retain common original rigid coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) (Q : WholePartition family B)

/-- A geometric subdivision of actual whole-roof cells, with every original cell covered.
No metric comparison or retained-copy correspondence is part of this data. -/
structure Refinement where
  parent : B → A
  included : ∀ b, Q.footprint b ⊆ P.footprint (parent b)
  cover : ∀ a, P.footprint a = ⋃ b : {b // parent b = a}, Q.footprint b.val

namespace Refinement

variable {P Q} (R : P.Refinement Q)

/-- Fine pieces in the original parent support's rigid planar coordinates. -/
def commonCell (a : A) (b : {b // R.parent b = a}) : Set Plane :=
  (family (P.support a)).project.symm '' Q.footprint b.val

theorem commonCell_closed (a : A) (b : {b // R.parent b = a}) :
    IsClosed (R.commonCell a b) :=
  (family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _
    (Q.closed b.val)

theorem commonCell_convex (a : A) (b : {b // R.parent b = a}) :
    Convex ℝ (R.commonCell a b) :=
  (Q.convex b.val).affine_image (family (P.support a)).project.symm.toAffineMap

theorem commonCell_full (a : A) (b : {b // R.parent b = a}) :
    (interior (R.commonCell a b)).Nonempty := by
  change (interior ((family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    Q.footprint b.val)).Nonempty
  rw [← Homeomorph.image_interior]
  exact (Q.full b.val).image _

theorem commonCell_cover (a : A) : P.planarCell a = ⋃ b, R.commonCell a b := by
  change (family (P.support a)).project.symm '' P.footprint a = _
  rw [R.cover a, Set.image_iUnion]
  rfl

/-- Original coarse and fine supports place every common-coordinate piece on the same roof. -/
theorem commonCell_place_image (a : A) (b : {b // R.parent b = a}) :
    (family (P.support a)).place '' R.commonCell a b = Q.spatialCell b.val := by
  have parent_active (p : Plane) (member : p ∈ Q.footprint b.val) :
      height family p = (family (P.support a)).height p := by
    apply P.active a p
    exact Eq.mp (congrArg (fun k => p ∈ P.footprint k) b.property) (R.included b.val member)
  apply Set.Subset.antisymm
  · rintro z ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨(family (Q.support b.val)).project.symm p, ⟨p, hp, rfl⟩, ?_⟩
    exact (point_eq_place family (Q.support b.val) (Q.active b.val p hp)).symm.trans
      (point_eq_place family (P.support a) (parent_active p hp))
  · rintro z ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨(family (P.support a)).project.symm p, ⟨p, hp, rfl⟩, ?_⟩
    exact (point_eq_place family (P.support a) (parent_active p hp)).symm.trans
      (point_eq_place family (Q.support b.val) (Q.active b.val p hp))

/-- Original horizontal boundary cuts remain boundary cuts in the parent's rigid coordinates. -/
theorem commonRegion_cut_disjoint_interior (cuts : Set Plane)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) (a : A) :
    Disjoint (interior (P.planarCell a))
      ((family (P.support a)).place ⁻¹' (Cap.horizontal ⁻¹' cuts)) := by
  apply Set.disjoint_left.mpr
  intro z inside on_cut
  change z ∈ interior ((family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    P.footprint a) at inside
  rw [← Homeomorph.image_interior] at inside
  obtain ⟨p, hp, rfl⟩ := inside
  have cut : Cap.horizontal ((family (P.support a)).place
      ((family (P.support a)).project.symm p)) ∈ cuts := on_cut
  rw [(family (P.support a)).horizontal_place,
    (family (P.support a)).project.apply_symm_apply] at cut
  exact Set.disjoint_left.mp (outside a) hp cut

variable [Finite A] [Finite B]

/-- Actual geometric whole-roof refinements supply all local physical cut metric data. -/
def physicalCutRefinement (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) :
    MetricGluing.PhysicalCutRefinement P.spatialCell Q.spatialCell Q.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) :=
  MetricGluing.flatPhysicalCutRefinement P.spatialCell Q.spatialCell Q.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) R.parent (fun a => (family (P.support a)).place)
    (fun a => (family (P.support a)).place.isometry) P.planarCell R.commonCell
    R.commonCell_closed R.commonCell_convex R.commonCell_full P.convex_planarCell
    R.commonCell_cover (fun _ => rfl) R.commonCell_place_image
    (fun a => (cut_closed.preimage Cap.horizontalCLM.continuous).preimage
      (family (P.support a)).place.continuous)
    (commonRegion_cut_disjoint_interior (P := P) cuts outside)

end Refinement
end Unfoldings.SpatialEnvelope.WholePartition
