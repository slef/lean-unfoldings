module

public import Unfoldings.Geometry.SpatialEnvelopeWholeGluing
public import Unfoldings.Geometry.AffineEnvelopeWholePartition
public import Unfoldings.Metric.PolygonalBoundaryCover
public import Unfoldings.Geometry.AffineSupportBoundary

/-! Full unbounded active-plane partitions of the physical roof aligned to prescribed lines. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

universe u

variable {I : Type u} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

/-- An actual partition of the whole envelope's horizontal plane into active supporting pieces. -/
structure WholePartition (A : Type u) where
  footprint : A → Set Plane
  support : A → I
  closed : ∀ a, IsClosed (footprint a)
  convex : ∀ a, Convex ℝ (footprint a)
  full : ∀ a, (interior (footprint a)).Nonempty
  disjoint : ∀ a b, a ≠ b → Disjoint (interior (footprint a)) (interior (footprint b))
  cover : (⋃ a, footprint a) = Set.univ
  active : ∀ a p, p ∈ footprint a → height family p = (family (support a)).height p

/-- Every finite set of proper cut-support lines admits a full unbounded active-plane partition. -/
theorem exists_wholePartition {J : Type u} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, extra j ≠ 0) :
    ∃ (A : Type u) (_ : Fintype A) (P : WholePartition family A) (signs : A → J → Bool),
      ∀ a p, p ∈ P.footprint a → ∀ j,
        0 ≤ AffineArrangement.signed (extra j) (signs a j) p := by
  obtain ⟨A, inst, cells, support, signs, properties, disjoint, cover, active, constrained⟩ :=
    AffineEnvelope.exists_whole_constrained_cell_partition (fun i => (family i).height) extra proper
  exact ⟨A, inst, ⟨cells, support, fun a => (properties a).1,
    fun a => (properties a).2.1, fun a => (properties a).2.2, disjoint, cover, active⟩,
    signs, constrained⟩

namespace WholePartition

variable {family} {A : Type u} (P : WholePartition family A)

/-- Each piece uses the original supporting plane's rigid Euclidean coordinates. -/
def planarCell (a : A) : Set Plane := (family (P.support a)).project.symm '' P.footprint a

/-- The entire corresponding spatial piece of the original physical graph. -/
def spatialCell (a : A) : Set Space := (family (P.support a)).place '' P.planarCell a

theorem isClosed_planarCell (a : A) : IsClosed (P.planarCell a) :=
  (family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _
    (P.closed a)

theorem convex_planarCell (a : A) : Convex ℝ (P.planarCell a) :=
  Convex.affine_image (family (P.support a)).project.symm.toAffineMap (P.convex a)

theorem planarCell_interior_nonempty (a : A) : (interior (P.planarCell a)).Nonempty := by
  change (interior ((family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    P.footprint a)).Nonempty
  rw [← Homeomorph.image_interior]
  exact (P.full a).image _

theorem isClosed_spatialCell (a : A) : IsClosed (P.spatialCell a) :=
  (family (P.support a)).place.isometry.isClosedEmbedding.isClosedMap _ (P.isClosed_planarCell a)

theorem convex_spatialCell (a : A) : Convex ℝ (P.spatialCell a) :=
  Convex.affine_image (family (P.support a)).place.toAffineMap (P.convex_planarCell a)

/-- No piece of the physical graph is removed or added by this partition. -/
theorem wholeSurface_eq_iUnion_spatialCell : wholeSurface family = ⋃ a, P.spatialCell a := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have covered : p ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ p
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp covered
    exact Set.mem_iUnion.mpr ⟨a, (family (P.support a)).project.symm p,
      ⟨p, ha, rfl⟩, (point_eq_place family (P.support a) (P.active a p ha)).symm⟩
  · intro member
    obtain ⟨a, x, ⟨p, hp, rfl⟩, rfl⟩ := Set.mem_iUnion.mp member
    exact ⟨p, point_eq_place family (P.support a) (P.active a p hp)⟩

/-- The rigid supporting plane identifies the actual planar and spatial partition cells. -/
def cellIsometryEquiv (a : A) : P.planarCell a ≃ᵢ P.spatialCell a where
  toEquiv := Equiv.ofBijective
    (fun x => (⟨(family (P.support a)).place x.val, x.val, x.property, rfl⟩ : P.spatialCell a))
    (by
      constructor
      · intro x y equal
        exact Subtype.ext ((family (P.support a)).place.injective (congrArg Subtype.val equal))
      · rintro ⟨z, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  isometry_toFun := fun x y => (family (P.support a)).place.isometry x.val y.val

/-- Only different partition cells declare their physical common points as seams. -/
def glue := MetricGluing.reparametrizeGlue P.cellIsometryEquiv
  (MetricGluing.distinctCoincident P.spatialCell)

@[simp] theorem glue_iff (x y : MetricGluing.Total (fun a => P.planarCell a)) :
    P.glue x y ↔ x.1 ≠ y.1 ∧
      (family (P.support x.1)).place x.2.val = (family (P.support y.1)).place y.2.val := Iff.rfl

/-- The partition gluing has exactly the actual intrinsic metric on the whole roof. -/
def intrinsicIsometryEquiv [Finite A] :
    MetricGluing.Realization (fun a => P.planarCell a) P.glue ≃ᵢ
      PolygonalPoint (wholeSurface family) :=
  (MetricGluing.reparametrizeIsometryEquiv P.cellIsometryEquiv
    (MetricGluing.distinctCoincident P.spatialCell)).trans
    (MetricGluing.boundaryCoverIsometryEquiv P.spatialCell P.isClosed_spatialCell
      P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell)

@[simp] theorem intrinsicIsometryEquiv_of [Finite A] (a : A) (x : P.planarCell a) :
    (P.intrinsicIsometryEquiv (MetricGluing.of (fun a => P.planarCell a) P.glue a x)).val =
      (family (P.support a)).place x.val := rfl

/-- Actual horizontal coordinates detect every physical seam. -/
theorem horizontal_mem_footprint (a : A) (x : P.planarCell a) :
    Cap.horizontal ((family (P.support a)).place x.val) ∈ P.footprint a := by
  obtain ⟨p, hp, equal⟩ := x.property
  rw [(family (P.support a)).horizontal_place, ← equal,
    (family (P.support a)).project.apply_symm_apply]
  exact hp

/-- All actual physical seams occur on planar cell boundaries. -/
theorem seamSupport_boundary (a : A) (x : P.planarCell a)
    (seam : x ∈ MetricGluing.seamSupport (fun a => P.planarCell a) P.glue a) :
    x.val ∉ interior (P.planarCell a) := by
  have separated (b : A) (different : a ≠ b) :
      Disjoint (interior (P.footprint a)) (P.footprint b) := by
    have regular : closure (interior (P.footprint b)) = P.footprint b := by
      rw [(P.convex b).closure_interior_eq_closure_of_nonempty_interior (P.full b),
        (P.closed b).closure_eq]
    rw [← regular]
    exact (P.disjoint a b different).closure_right isOpen_interior
  intro inside
  have horizontal_inside : Cap.horizontal ((family (P.support a)).place x.val) ∈
      interior (P.footprint a) := by
    change x.val ∈ interior
      ((family (P.support a)).project.symm.toContinuousAffineEquiv.toHomeomorph ''
        P.footprint a) at inside
    rw [← Homeomorph.image_interior] at inside
    obtain ⟨p, hp, equal⟩ := inside
    change (family (P.support a)).project.symm p = x.val at equal
    rw [(family (P.support a)).horizontal_place, ← equal,
      (family (P.support a)).project.apply_symm_apply]
    exact hp
  rcases seam with ⟨⟨b, y⟩, joined⟩ | ⟨⟨b, y⟩, joined⟩
  · obtain ⟨different, equal⟩ := (P.glue_iff _ _).mp joined
    apply Set.disjoint_left.mp (separated b different) horizontal_inside
    rw [equal]
    exact P.horizontal_mem_footprint b y
  · obtain ⟨different, equal⟩ := (P.glue_iff _ _).mp joined
    apply Set.disjoint_left.mp (separated b (Ne.symm different)) horizontal_inside
    rw [← equal]
    exact P.horizontal_mem_footprint b y

/-- The whole partition realization is complete, with its constructed intrinsic metric. -/
theorem completeSpace_realization [Finite A] :
    CompleteSpace (MetricGluing.Realization (fun a => P.planarCell a) P.glue) := by
  let : CompleteSpace (PolygonalPoint (wholeSurface family)) := wholeSurface_complete family
  exact P.intrinsicIsometryEquiv.completeSpace

/-- Its topology is that of the entire original plane, including all unbounded ends. -/
def planeHomeomorph [Finite A] :
    MetricGluing.Realization (fun a => P.planarCell a) P.glue ≃ₜ Plane :=
  P.intrinsicIsometryEquiv.toHomeomorph.trans (wholeSurfacePlaneHomeomorph family)

theorem contractibleSpace_realization [Finite A] :
    ContractibleSpace (MetricGluing.Realization (fun a => P.planarCell a) P.glue) :=
  P.planeHomeomorph.contractibleSpace

/-- Every prescribed supporting line lies in the actual partition frontiers. -/
theorem mem_frontier_of_constraint {J : Type*} (extra : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, extra j ≠ 0) (signs : A → J → Bool)
    (constrained : ∀ a p, p ∈ P.footprint a → ∀ j,
      0 ≤ AffineArrangement.signed (extra j) (signs a j) p)
    (a : A) {p : Plane} (member : p ∈ P.footprint a) (j : J) (zero : extra j p = 0) :
    p ∈ frontier (P.footprint a) := by
  refine ⟨subset_closure member, ?_⟩
  apply not_mem_interior_of_affine_lower_bound
    (AffineArrangement.signed (extra j) (signs a j))
  · cases value : signs a j <;> simpa [AffineArrangement.signed, value] using proper j
  · exact fun x hx => constrained a x hx j
  · simp only [AffineArrangement.signed_apply, zero, neg_zero, ite_self]

end WholePartition
end Unfoldings.SpatialEnvelope
