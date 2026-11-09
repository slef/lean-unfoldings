module

public import Unfoldings.Source.UniqueProjection
public import Unfoldings.Source.ContinuousCoordinates

/-!
# Constructed continuous source coordinates on the cut-locus complement

Compactness proves that the unique shortest path depends continuously on its
endpoint off the cut locus. Its actual source vector thus gives continuous
coordinates there. Injectivity follows whenever whole-path source vectors are
injective, as proved for actual convex boundaries. Local isometry is separate.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X}
  (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

def coordinatesOffCutLocus (x : ↥((sourceCutLocus source)ᶜ)) : Plane :=
  let p := (SourcePath.offCutLocusHomeomorph exists_paths).symm x
  R.coordinate p.val.path p.val.geodesic

theorem continuous_coordinatesOffCutLocus : Continuous (R.coordinatesOffCutLocus exists_paths) :=
  R.continuous_coordinate.comp (continuous_subtype_val.comp
    (SourcePath.offCutLocusHomeomorph exists_paths).symm.continuous)

theorem coordinatesOffCutLocus_injective
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    Function.Injective (R.coordinatesOffCutLocus exists_paths) := by
  intro x y equal
  apply (SourcePath.offCutLocusHomeomorph exists_paths).symm.injective
  apply Subtype.ext
  exact injective equal

theorem norm_coordinatesOffCutLocus (x : ↥((sourceCutLocus source)ᶜ)) :
    ‖R.coordinatesOffCutLocus exists_paths x‖ = dist source x.val := by
  let p := (SourcePath.offCutLocusHomeomorph exists_paths).symm x
  have target : p.val.target = x.val :=
    congrArg Subtype.val ((SourcePath.offCutLocusHomeomorph exists_paths).apply_symm_apply x)
  exact (R.norm_coordinate p.val.path p.val.geodesic).trans (congrArg (dist source) target)

end Unfoldings.SourceFrame
