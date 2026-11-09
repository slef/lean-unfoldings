module

public import Unfoldings.Source.ContinuousCoordinates
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual planar domain of shortest-path source vectors

When source vectors distinguish shortest paths, compactness identifies the
whole path space homeomorphically with its closed planar image. Endpoint
evaluation defines a continuous projection back to the original surface.
Different tied paths retain different planar points over the same endpoint.
Local metric compatibility and the cut-locus boundary require further proofs.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)

def domain : Set Plane := Set.range (fun p : SourcePath source => R.coordinate p.path p.geodesic)

theorem compact_domain : IsCompact R.domain := R.compact_coordinate_range

theorem closed_domain : IsClosed R.domain := R.compact_domain.isClosed

def coordinateHomeomorph
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    SourcePath source ≃ₜ R.domain :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective (fun p : SourcePath source => R.coordinate p.path p.geodesic) injective)
    (R.continuous_coordinate.subtype_mk _)

@[simp] theorem coordinateHomeomorph_apply
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (p : SourcePath source) :
    (R.coordinateHomeomorph injective p).val = R.coordinate p.path p.geodesic := rfl

def projection
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    R.domain → X := fun z => ((R.coordinateHomeomorph injective).symm z).target

theorem continuous_projection
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    Continuous (R.projection injective) :=
  SourcePath.continuous_target.comp (R.coordinateHomeomorph injective).symm.continuous

@[simp] theorem projection_coordinateHomeomorph
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (p : SourcePath source) : R.projection injective (R.coordinateHomeomorph injective p) =
      p.target := congrArg SourcePath.target ((R.coordinateHomeomorph injective).symm_apply_apply p)

theorem norm_eq_projection_distance
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (z : R.domain) : ‖z.val‖ = dist source (R.projection injective z) := by
  let p := (R.coordinateHomeomorph injective).symm z
  have equal : R.coordinate p.path p.geodesic = z.val :=
    congrArg Subtype.val ((R.coordinateHomeomorph injective).apply_symm_apply z)
  rw [← equal, R.norm_coordinate]
  rfl

theorem projection_surjective
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (exists_paths : Function.Surjective (SourcePath.target (source := source))) :
    Function.Surjective (R.projection injective) := by
  intro x
  obtain ⟨p, rfl⟩ := exists_paths x
  exact ⟨R.coordinateHomeomorph injective p, R.projection_coordinateHomeomorph injective p⟩

end Unfoldings.SourceFrame
