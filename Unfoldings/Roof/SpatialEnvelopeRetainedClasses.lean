module

public import Unfoldings.Geometry.SpatialEnvelopeCuts
public import Unfoldings.Roof.SpatialEnvelopeRoof

/-! Actual auxiliary seam classes survive away from the prescribed geometric cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialClassesIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem projectFace_eq_of_paired_related {a b : T.pairedComplex.Total}
    (related : Relation.EqvGen (T.pairedComplex.glue Set.univ) a b) :
    (family (T.support a.1)).project a.2.val = (family (T.support b.1)).project b.2.val := by
  have equal := congrArg (fun p => Cap.horizontal (T.pairedFolding.toSpace Set.univ p))
    ((T.pairedComplex.point_eq_iff Set.univ a b).mpr related)
  change Cap.horizontal (T.placement a.1 a.2.val) =
    Cap.horizontal (T.placement b.1 b.2.val) at equal
  dsimp only [placement] at equal
  rwa [(family (T.support a.1)).horizontal_place,
    (family (T.support b.1)).horizontal_place] at equal

theorem related_away_cuts (cuts : Set Plane) {a b : T.pairedComplex.Total}
    (related : Relation.EqvGen (T.pairedComplex.glue Set.univ) a b)
    (outside : (family (T.support a.1)).project a.2.val ∉ cuts) :
    Relation.EqvGen (T.pairedComplex.glue (T.retainOutside cuts)) a b := by
  induction related with
  | rel a b joined =>
    obtain ⟨s, _kept, x, rfl, rfl⟩ := joined
    apply Relation.EqvGen.rel
    refine ⟨s, ?_, x, rfl, rfl⟩
    intro selected
    exact outside (selected ((T.edgeProjection
      (T.pairedComplex.left s).face (T.pairedComplex.left s).edge) x).property)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b related ih =>
    have avoid : (family (T.support a.1)).project a.2.val ∉ cuts := by
      rwa [T.projectFace_eq_of_paired_related related]
    exact (ih avoid).symm
  | trans a b c first _last ih₁ ih₂ =>
    have avoid : (family (T.support b.1)).project b.2.val ∉ cuts := by
      rwa [← T.projectFace_eq_of_paired_related first]
    exact Relation.EqvGen.trans _ _ _ (ih₁ outside) (ih₂ avoid)

theorem paired_related_of_projection_eq
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    {a b : T.pairedComplex.Total}
    (same : (family (T.support a.1)).project a.2.val =
      (family (T.support b.1)).project b.2.val) :
    Relation.EqvGen (T.pairedComplex.glue Set.univ) a b := by
  apply (T.pairedComplex.point_eq_iff Set.univ a b).mp
  apply T.pairedProjection_injective conforming
  change Cap.horizontal ((family (T.support a.1)).place a.2.val) =
    Cap.horizontal ((family (T.support b.1)).place b.2.val)
  rwa [(family (T.support a.1)).horizontal_place,
    (family (T.support b.1)).horizontal_place]

end Unfoldings.SpatialEnvelope.Triangulation
