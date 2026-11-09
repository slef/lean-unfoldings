module

public import Unfoldings.Source.FiniteMotions

/-!
# Finite virtual source images for actual retained endpoints

The inverse rigid motions send the developed source to finitely many points
in original face coordinates. Actual source distance at a retained endpoint
equals distance to one of these constructed images. A minimum over arbitrary
candidate images is not asserted: feasibility and cut-boundary descriptions
require further proofs.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem source_distance_eq_motion_image :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      (x : P.sourceFaceRegion source f),
      dist source (C.faceMap Set.univ f x.val) =
        dist x.val.val ((P.sourceFaceMotion R f x).symm 0) := by
  let := P.metricSpace
  intro source R f x
  have norm_equal : ‖P.sourceFaceCoordinates R f x‖ = dist source (C.faceMap Set.univ f x.val) :=
    R.norm_coordinatesOffCutLocus (P.sourcePath_target_surjective source) ⟨_, x.property⟩
  rw [← norm_equal, P.sourceFaceCoordinates_eq_motion R f x]
  rw [← (P.sourceFaceMotion R f x).isometry.dist_eq x.val.val
    ((P.sourceFaceMotion R f x).symm 0), AffineIsometryEquiv.apply_symm_apply, dist_zero_right]

theorem exists_finite_source_images :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source),
      ∃ V : Set Plane, V.Finite ∧ ∀ (f : Face) (x : P.sourceFaceRegion source f),
        ∃ v ∈ V, dist source (C.faceMap Set.univ f x.val) = dist x.val.val v := by
  let := P.metricSpace
  intro source R
  obtain ⟨M, finite, covers⟩ := P.exists_finite_actual_source_motions R
  let V := (fun A : Plane ≃ᵃⁱ[ℝ] Plane => A.symm 0) '' M
  refine ⟨V, finite.image _, ?_⟩
  intro f x
  refine ⟨(P.sourceFaceMotion R f x).symm 0, ?_, P.source_distance_eq_motion_image R f x⟩
  exact ⟨P.sourceFaceMotion R f x, covers ⟨f, x.val⟩ x.property, rfl⟩

end Unfoldings.SpatialFolding.ConvexBoundary
