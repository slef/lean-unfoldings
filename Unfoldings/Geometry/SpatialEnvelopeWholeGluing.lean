module

public import Unfoldings.Geometry.SpatialEnvelopeWholeMetric
public import Unfoldings.Metric.PolygonalCoverGluing
public import Unfoldings.Metric.Reparametrize

/-! The entire physical roof as an exact metric gluing of its rigid planar cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

/-- Active supporting cells in the plane's actual rigid Euclidean coordinates. -/
def wholePlanarCell (i : I) : Set Plane :=
  (family i).project.symm '' AffineEnvelope.cell (fun j => (family j).height) i

omit [Fintype I] [Nonempty I] in
theorem isClosed_wholePlanarCell (i : I) : IsClosed (wholePlanarCell family i) :=
  (family i).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _
    (AffineEnvelope.isClosed_cell _ i)

omit [Fintype I] [Nonempty I] in
theorem convex_wholePlanarCell (i : I) : Convex ℝ (wholePlanarCell family i) :=
  Convex.affine_image (family i).project.symm.toAffineMap (AffineEnvelope.convex_cell _ i)

/-- Rigid placement is an exact isometry onto the actual entire spatial cell. -/
def wholeCellIsometryEquiv (i : I) : wholePlanarCell family i ≃ᵢ wholeCell family i where
  toEquiv := Equiv.ofBijective
    (fun x => (⟨(family i).place x.val, x.val, x.property, rfl⟩ : wholeCell family i))
    (by
      constructor
      · intro x y equal
        exact Subtype.ext ((family i).place.injective (congrArg Subtype.val equal))
      · rintro ⟨z, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  isometry_toFun := fun x y => (family i).place.isometry x.val y.val

/-- All original physical coincidences, expressed in rigid planar cell coordinates. -/
def wholePlanarGlue :=
  MetricGluing.reparametrizeGlue (wholeCellIsometryEquiv family)
    (MetricGluing.coincident (wholeCell family))

omit [Fintype I] [Nonempty I] in
@[simp] theorem wholePlanarGlue_iff
    (x y : MetricGluing.Total (fun i => wholePlanarCell family i)) :
    wholePlanarGlue family x y ↔
      (family x.1).place x.2.val = (family y.1).place y.2.val := Iff.rfl

/-- The exact unbounded intrinsic roof, represented by actual planar cells and physical seams. -/
def wholePlanarGluingIsometryEquiv :
    MetricGluing.Realization (fun i => wholePlanarCell family i) (wholePlanarGlue family) ≃ᵢ
      PolygonalPoint (wholeSurface family) :=
  (MetricGluing.reparametrizeIsometryEquiv (wholeCellIsometryEquiv family)
    (MetricGluing.coincident (wholeCell family))).trans
    (MetricGluing.closedCoverIsometryEquiv (wholeCell family) (isClosed_wholeCell family)
      (convex_wholeCell family) (wholeSurface_eq_iUnion_cells family))

/-- Changing cell coordinates retains the proved topology of the whole plane. -/
def wholePlanarGluingPlaneHomeomorph :
    MetricGluing.Realization (fun i => wholePlanarCell family i)
      (wholePlanarGlue family) ≃ₜ Plane :=
  (wholePlanarGluingIsometryEquiv family).toHomeomorph.trans (wholeSurfacePlaneHomeomorph family)

omit [Fintype I] in
theorem wholePlanarGluing_contractible [Finite I] :
    ContractibleSpace
      (MetricGluing.Realization (fun i => wholePlanarCell family i) (wholePlanarGlue family)) := by
  let : Fintype I := Fintype.ofFinite I
  exact (wholePlanarGluingPlaneHomeomorph family).contractibleSpace

omit [Fintype I] in
theorem wholePlanarGluing_complete [Finite I] :
    CompleteSpace
      (MetricGluing.Realization (fun i => wholePlanarCell family i) (wholePlanarGlue family)) := by
  let : Fintype I := Fintype.ofFinite I
  let : CompleteSpace (PolygonalPoint (wholeSurface family)) := wholeSurface_complete family
  exact (wholePlanarGluingIsometryEquiv family).completeSpace_iff.mpr inferInstance

end Unfoldings.SpatialEnvelope
