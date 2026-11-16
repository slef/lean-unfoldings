module

public import Unfoldings.Geometry.SpatialGraphPartition
public import Unfoldings.Metric.FlatPhysicalCutRefinement

/-! Geometric subdivisions of a physical graph patch preserve its actual cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialGraphPartition

universe u v

variable {height : Plane → ℝ} {region : Set Plane} {A : Type u} {B : Type v}
  (P : SpatialGraphPartition height region A) (Q : SpatialGraphPartition height region B)

/-- An actual subdivision on a common graph patch, with no shared support-label requirement. -/
structure Refinement where
  parent : B → A
  included : ∀ b, Q.footprint b ⊆ P.footprint (parent b)
  cover : ∀ a, P.footprint a = ⋃ b : {b // parent b = a}, Q.footprint b.val

namespace Refinement

variable {P Q} (R : P.Refinement Q)

def commonCell (a : A) (b : {b // R.parent b = a}) : Set Plane :=
  (P.plane a).project.symm '' Q.footprint b.val

theorem commonCell_closed (a : A) (b : {b // R.parent b = a}) : IsClosed (R.commonCell a b) :=
  (P.plane a).project.symm.toContinuousAffineEquiv.toHomeomorph.isClosedMap _ (Q.closed b.val)

theorem commonCell_convex (a : A) (b : {b // R.parent b = a}) : Convex ℝ (R.commonCell a b) :=
  (Q.convex b.val).affine_image (P.plane a).project.symm.toAffineMap

theorem commonCell_full (a : A) (b : {b // R.parent b = a}) :
    (interior (R.commonCell a b)).Nonempty := by
  change (interior ((P.plane a).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    Q.footprint b.val)).Nonempty
  rw [← Homeomorph.image_interior]
  exact (Q.full b.val).image _

theorem commonCell_cover (a : A) : P.planarCell a = ⋃ b, R.commonCell a b := by
  change (P.plane a).project.symm '' P.footprint a = _
  rw [R.cover a, Set.image_iUnion]
  rfl

/-- The two original rigid frames place every common point on the identical physical graph. -/
theorem commonCell_place_image (a : A) (b : {b // R.parent b = a}) :
    (P.plane a).place '' R.commonCell a b = Q.spatialCell b.val := by
  have parent_member (p : Q.footprint b.val) : p.val ∈ P.footprint a :=
    Eq.mp (congrArg (fun k => p.val ∈ P.footprint k) b.property) (R.included b.val p.property)
  apply Set.Subset.antisymm
  · rintro z ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨(Q.plane b.val).project.symm p, ⟨p, hp, rfl⟩, ?_⟩
    exact (Q.place_eq_graph b.val ⟨p, hp⟩).trans
      (P.place_eq_graph a ⟨p, parent_member ⟨p, hp⟩⟩).symm
  · rintro z ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨(P.plane a).project.symm p, ⟨p, hp, rfl⟩, ?_⟩
    exact (P.place_eq_graph a ⟨p, parent_member ⟨p, hp⟩⟩).trans
      (Q.place_eq_graph b.val ⟨p, hp⟩).symm

/-- Geometric boundary cuts remain boundary cuts in the original parent coordinates. -/
theorem commonRegion_cut_disjoint_interior (cuts : Set Plane)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) (a : A) :
    Disjoint (interior (P.planarCell a)) ((P.plane a).place ⁻¹' (Cap.horizontal ⁻¹' cuts)) := by
  apply Set.disjoint_left.mpr
  intro z inside on_cut
  change z ∈ interior ((P.plane a).project.symm.toContinuousAffineEquiv.toHomeomorph ''
    P.footprint a) at inside
  rw [← Homeomorph.image_interior] at inside
  obtain ⟨p, hp, rfl⟩ := inside
  have cut : Cap.horizontal ((P.plane a).place ((P.plane a).project.symm p)) ∈ cuts := on_cut
  rw [(P.plane a).horizontal_place, (P.plane a).project.apply_symm_apply] at cut
  exact Set.disjoint_left.mp (outside a) hp cut

variable [Finite A] [Finite B]

/-- All local spatial cut data are derived from the actual graph subdivision. -/
def physicalCutRefinement (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) :
    MetricGluing.PhysicalCutRefinement P.spatialCell Q.spatialCell Q.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) :=
  MetricGluing.flatPhysicalCutRefinement P.spatialCell Q.spatialCell Q.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) R.parent (fun a => (P.plane a).place)
    (fun a => (P.plane a).place.isometry) P.planarCell R.commonCell
    R.commonCell_closed R.commonCell_convex R.commonCell_full P.convex_planarCell
    R.commonCell_cover (fun _ => rfl) R.commonCell_place_image
    (fun a => (cut_closed.preimage Cap.horizontalCLM.continuous).preimage
      (P.plane a).place.continuous)
    (commonRegion_cut_disjoint_interior (P := P) cuts outside)

/-- Subdivision preserves the entire physical patch cut, including all original bank copies. -/
def cutEquiv (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) : Q.Cut cuts ≃ᵢ P.Cut cuts :=
  (R.physicalCutRefinement cuts cut_closed outside).isometryEquiv P.isClosed_spatialCell

theorem fold_cutEquiv (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) (x : Q.Cut cuts) :
    P.fold cuts (R.cutEquiv cuts cut_closed outside x) = Q.fold cuts x :=
  (R.physicalCutRefinement cuts cut_closed outside).fold_isometryEquiv P.isClosed_spatialCell x

/-- The metric equivalence keeps the literal physical lift in its specified parent cell. -/
theorem cutEquiv_liftCell (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside : ∀ a, Disjoint (interior (P.footprint a)) cuts) (b : B) (p : Q.footprint b) :
    R.cutEquiv cuts cut_closed outside (Q.liftCell cuts b p) =
      P.liftCell cuts (R.parent b) ⟨p.val, R.included b p.property⟩ :=
  ((R.physicalCutRefinement cuts cut_closed outside).isometryEquiv_of
    P.isClosed_spatialCell b _).trans
    (congrArg (MetricGluing.of (fun a => P.spatialCell a)
      (MetricGluing.cutSeams P.spatialCell P.isClosed_spatialCell
        (Cap.horizontal ⁻¹' cuts)).relation
      (R.parent b)) (Subtype.ext ((Q.place_eq_graph b p).trans
        (P.place_eq_graph (R.parent b) ⟨p.val, R.included b p.property⟩).symm)))

end Refinement
end Unfoldings.SpatialGraphPartition
