module

public import Unfoldings.Source.Coordinates
public import Unfoldings.Source.ShortestPath
public import Unfoldings.Polyhedron.GeodesicRegularity

/-!
# Initial planar vectors distinguish all convex-boundary shortest paths

The coordinates are constructed in an actual regular source chart. Their
norm recovers endpoint distance, and equal vectors force initial agreement.
The proved regularity of geodesic interiors then gives equality everywhere,
including for tied shortest paths to one cut-locus endpoint.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem geodesics_eq_of_source_coordinate_eq :
    letI := P.metricSpace
    ∀ {source a b : C.Realization Set.univ}
    (R : SourceFrame source) {p : Path source a} {q : Path source b}
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic)
    (_equal : R.coordinate p geodesic = R.coordinate q other), ∀ t, p t = q t := by
  let := P.metricSpace
  intro source a b R p q geodesic other equal
  by_cases distinct : source ≠ a
  · exact P.geodesics_eq_of_initial_interval geodesic other distinct
      (R.initial_eq_of_coordinate_eq geodesic other equal)
  · have first : a = source := not_ne_iff.mp distinct |>.symm
    have distance : dist source a = dist source b :=
      (R.norm_coordinate p geodesic).symm.trans
        ((congrArg norm equal).trans (R.norm_coordinate q other))
    have last : b = source := by
      rw [first, dist_self] at distance
      exact (dist_eq_zero.mp distance.symm).symm
    intro t
    have at_p : p t = source := dist_eq_zero.mp (by
      rw [dist_comm, geodesic.dist_source, first, dist_self, zero_mul])
    have at_q : q t = source := dist_eq_zero.mp (by
      rw [dist_comm, other.dist_source, last, dist_self, zero_mul])
    exact at_p.trans at_q.symm

def sourcePathCoordinate :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → SourceFrame source → SourcePath source → Plane := by
  let := P.metricSpace
  intro source R p
  exact R.coordinate p.path p.geodesic

theorem sourcePathCoordinate_injective :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      Function.Injective (P.sourcePathCoordinate R) := by
  let := P.metricSpace
  intro source R p q equal
  exact SourcePath.ext (P.geodesics_eq_of_source_coordinate_eq R p.geodesic q.geodesic equal)

theorem norm_sourcePathCoordinate :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (p : SourcePath source),
      ‖P.sourcePathCoordinate R p‖ = dist source p.target := by
  let := P.metricSpace
  intro source R p
  exact R.norm_coordinate p.path p.geodesic

theorem sourcePath_target_surjective (source : C.Realization Set.univ) :
    letI := P.metricSpace
    Function.Surjective (SourcePath.target (source := source)) := by
  let := P.metricSpace
  intro target
  obtain ⟨p, geodesic⟩ := P.exists_geodesic source target
  exact ⟨⟨target, p, geodesic⟩, rfl⟩

end Unfoldings.SpatialFolding.ConvexBoundary
