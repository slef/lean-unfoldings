module

public import Unfoldings.Source.CutMetric
public import Unfoldings.Source.RegularDevelopment
public import Unfoldings.Metric.PolygonalLocal
public import Unfoldings.Metric.LocalComposition
public import Unfoldings.Path.LocalDistance

/-!
# The source cut metric is the actual retained-surface path metric

Local source isometries and local polygonal charts give isometric
neighborhoods in both directions. Intrinsic continuous-path distance is
therefore preserved. Since the polygonal metric is already a length metric,
it is exactly path distance in the original regular retained surface.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceCutSurface_local_isometry :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (x : sourceRegularRegion source),
      ∃ T : Set (sourceRegularRegion source), IsOpen T ∧ x ∈ T ∧
        Isometry (fun y : T => P.sourceCutSurfaceHomeomorph R y.val) := by
  let := P.metricSpace
  intro source R x
  let H := P.sourceInteriorHomeomorph R
  let K := (PolygonalPoint.openHomeomorph (s := interior R.domain) isOpen_interior).symm
  have first : ∃ T : Set (sourceRegularRegion source), IsOpen T ∧ x ∈ T ∧
      Isometry (fun y : T => H y.val) := by
    obtain ⟨T, open_T, inside, isometry⟩ := P.regular_source_coordinates_local_isometry R x
    exact ⟨T, open_T, inside, fun a b => isometry a b⟩
  exact compose_isometric_neighborhood H K x first
    (PolygonalPoint.ofSubtype_isometric_neighborhood isOpen_interior (H x))

theorem sourceCutSurface_intrinsic_distance :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (a b : sourceRegularRegion source),
      edist (P.sourceCutSurfaceHomeomorph R a) (P.sourceCutSurfaceHomeomorph R b) =
        Path.eDistance a b := by
  let := P.metricSpace
  intro source R a b
  let := P.sourceCutInteriorMetric R
  let H := P.sourceCutSurfaceHomeomorph R
  have first := fun x => center_bound_of_isometric_neighborhood H x
    (P.sourceCutSurface_local_isometry R x)
  have last := fun y => center_bound_of_isometric_neighborhood H.symm y
    (inverse_isometric_neighborhood H y (P.sourceCutSurface_local_isometry R (H.symm y)))
  rw [← PolygonalPoint.eDistance_eq_edist]
  exact Path.eDistance_eq_of_homeomorph_local_center_bounds H first last a b

end Unfoldings.SpatialFolding.ConvexBoundary
