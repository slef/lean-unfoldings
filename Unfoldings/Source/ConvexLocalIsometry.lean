module

public import Unfoldings.Source.LocalIsometry
public import Unfoldings.Source.RegularUnique

/-! The actual convex-surface source coordinates are locally isometric
at every regular retained point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem source_coordinates_local_isometry_at_regular :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : ↥((sourceCutLocus source)ᶜ)), C.IsRegularPoint Set.univ x.val →
      ∃ S : Set ↥((sourceCutLocus source)ᶜ), IsOpen S ∧ x ∈ S ∧
        Isometry (fun y : S =>
          R.coordinatesOffCutLocus (P.sourcePath_target_surjective source) y.val) := by
  let := P.metricSpace
  intro source R x regular
  let exists_paths := P.sourcePath_target_surjective source
  let p := ((SourcePath.offCutLocusHomeomorph exists_paths).symm x).val
  have target : p.target = x.val := congrArg Subtype.val
    ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply x)
  have endpoint : C.IsRegularPoint Set.univ p.target := by rw [target]; exact regular
  exact R.exists_off_cut_isometry_near exists_paths x (P.sourcePath_all_regular R p endpoint)

end Unfoldings.SpatialFolding.ConvexBoundary
