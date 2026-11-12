module

public import Unfoldings.Cap.ClipInteriorSeams

/-! Full roof identifications away from a physical cut set survive its declared fine cuts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance retainedClassesIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem projectFace_eq_of_paired_related {a b : T.pairedComplex.Total}
    (related : Relation.EqvGen (T.pairedComplex.glue Set.univ) a b) :
    K.projectFace (T.face a.1) a.2.val = K.projectFace (T.face b.1) b.2.val :=
  congrArg (fun p => Cap.horizontal (T.pairedFolding.toSpace Set.univ p))
    ((T.pairedComplex.point_eq_iff Set.univ a b).mpr related)

theorem related_away_cuts (cuts : Set Plane) {a b : T.pairedComplex.Total}
    (related : Relation.EqvGen (T.pairedComplex.glue Set.univ) a b)
    (outside : K.projectFace (T.face a.1) a.2.val ∉ cuts) :
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
    have avoid : K.projectFace (T.face a.1) a.2.val ∉ cuts := by
      rwa [T.projectFace_eq_of_paired_related related]
    exact (ih avoid).symm
  | trans a b c first _last ih₁ ih₂ =>
    have avoid : K.projectFace (T.face b.1) b.2.val ∉ cuts := by
      rwa [← T.projectFace_eq_of_paired_related first]
    exact Relation.EqvGen.trans _ _ _ (ih₁ outside) (ih₂ avoid)

theorem paired_related_of_projection_eq
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    {a b : T.pairedComplex.Total}
    (same : K.projectFace (T.face a.1) a.2.val = K.projectFace (T.face b.1) b.2.val) :
    Relation.EqvGen (T.pairedComplex.glue Set.univ) a b := by
  apply (T.pairedComplex.faceMap_eq_iff Set.univ a.1 b.1 a.2 b.2).mp
  rw [← T.pointCopy_of_localPoint a.1 a.2, ← T.pointCopy_of_localPoint b.1 b.2]
  have first := T.pointCopy_eq conforming (K.projectFace (T.face a.1) a.2.val)
    (T.projected_member a.1 a.2.property)
    (same.symm ▸ T.projected_member b.1 b.2.property)
  exact first.trans (T.pointCopy_congr b.1 same _ _)

end Unfoldings.ConvexCap.ClipSpatialTriangles
