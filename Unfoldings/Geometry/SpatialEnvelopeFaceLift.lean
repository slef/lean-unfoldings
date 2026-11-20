module

public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Metric.ConvexPatchLift

/-! An original planar face has a canonical one-sided lift to the whole cut roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- Away from the prescribed cut, the restored physical point determines the entire cut copy. -/
theorem restoreCut_injective_at (cuts : Set Plane) {x y : P.Cut cuts}
    (equal : P.restoreCut cuts x = P.restoreCut cuts y)
    (outside : Cap.horizontal (P.restoreCut cuts x).val ∉ cuts) : x = y := by
  apply (P.cutIsometryEquiv cuts).injective
  exact MetricGluing.cutToPolygonal_injective_off_cuts P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) P.convex_spatialCell P.wholeSurface_eq_iUnion_spatialCell equal outside

/-- A placed convex face whose interior avoids the cuts lifts isometrically, including
its one-sided copies of the cut edges and corners. -/
theorem exists_cut_face_lift (cuts : Set Plane) (closed : IsClosed cuts)
    {s : Set Plane} (convex : Convex ℝ s) (full : (interior s).Nonempty)
    (place : Plane →ᵃⁱ[ℝ] Space) (contained : place '' s ⊆ wholeSurface family)
    (outside : ∀ x ∈ interior s, Cap.horizontal (place x) ∉ cuts) :
    ∃ lift : s → P.Cut cuts, Isometry lift ∧
      ∀ x, (P.restoreCut cuts (lift x)).val = place x.val := by
  let : CompleteSpace (P.Cut cuts) := P.cut_complete cuts
  let lifted (x : s) := PolygonalPoint.includeConvex (place '' s) contained
    (⟨place x.val, ⟨x.val, x.property, rfl⟩⟩ : place '' s)
  have spatial : Isometry lifted := by
    have to_image : Isometry (fun x : s =>
        (⟨place x.val, ⟨x.val, x.property, rfl⟩⟩ : place '' s)) :=
      fun x y => place.isometry x.val y.val
    exact (PolygonalPoint.includeConvex_isometry _ (convex.affine_image place.toAffineMap)
      contained).comp to_image
  have unique (x : interior s) : ∃! z, P.restoreCut cuts z =
      lifted ⟨x.val, interior_subset x.property⟩ := by
    obtain ⟨z, hz⟩ := P.restoreCut_surjective cuts (lifted ⟨x.val, interior_subset x.property⟩)
    refine ⟨z, hz, fun y hy => P.restoreCut_injective_at cuts (hy.trans hz.symm) ?_⟩
    rw [hy]
    exact outside x.val x.property
  obtain ⟨lift, isometric, agrees⟩ :=
    exists_isometric_convex_patch_lift convex full (P.restoreCut cuts)
      (P.restoreCut_lipschitz cuts) lifted spatial unique (by
        intro x z h
        apply P.exists_restoreCut_ball_isometry cuts closed z
        rw [h]
        exact outside x.val x.property)
  exact ⟨lift, isometric, fun x => congrArg PolygonalPoint.val (agrees x)⟩

end Unfoldings.SpatialEnvelope.WholePartition
