module

public import Unfoldings.Source.CutMetric

/-!
# Actual radial geodesics in the completed source net

Every original shortest path has its own completion point, including tied
endpoints. Its straight radial segment is a geodesic in the constructed cut
metric and projects pointwise to that original path. Source distances are
therefore preserved even at all boundary copies.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.SourceFrame

variable {X : Type*} [MetricSpace X] [CompactSpace X] {source : X} (R : SourceFrame source)

def cutPoint (p : SourcePath source) : R.cutCompletion :=
  ⟨R.coordinate p.path p.geodesic, ⟨p, rfl⟩⟩

def cutOrigin : R.cutCompletion := ⟨0, R.zero_mem_domain⟩

def cutRadial (p : SourcePath source) : Path R.cutOrigin (R.cutPoint p) :=
  PolygonalPoint.segmentPath (R.starConvex_domain.segment_subset (R.cutPoint p).property)

theorem cutRadial_isGeodesic (p : SourcePath source) : (R.cutRadial p).IsGeodesic :=
  PolygonalPoint.segmentPath_isGeodesic
    (R.starConvex_domain.segment_subset (R.cutPoint p).property)

theorem cutRadial_coordinate (p : SourcePath source) (t : unitInterval) :
    (R.cutRadial p t).val = (t : ℝ) • R.coordinate p.path p.geodesic := by
  change AffineMap.lineMap (0 : Plane) (R.coordinate p.path p.geodesic) (t : ℝ) = _
  simp only [AffineMap.lineMap_apply_module', sub_zero, add_zero]

theorem cutRadial_projection
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (p : SourcePath source) (t : unitInterval) :
    R.cutCompletionProjection injective (R.cutRadial p t) = p.path t := by
  have point : PolygonalPoint.toSubtype (R.cutRadial p t) =
      R.coordinateHomeomorph injective (p.initial t) := by
    apply Subtype.ext
    exact (R.cutRadial_coordinate p t).trans (R.coordinate_initial p t).symm
  change R.projection injective (PolygonalPoint.toSubtype (R.cutRadial p t)) = _
  rw [point, R.projection_coordinateHomeomorph]
  rfl

theorem cutOrigin_edist (z : R.cutCompletion) :
    edist R.cutOrigin z = ENNReal.ofReal ‖z.val‖ := by
  rw [PolygonalPoint.edist_eq_of_segment (R.starConvex_domain.segment_subset z.property)]
  exact edist_dist (0 : Plane) z.val |>.trans (by rw [dist_zero_left])

theorem cutOrigin_distance_preserved
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic))
    (z : R.cutCompletion) :
    edist R.cutOrigin z = edist source (R.cutCompletionProjection injective z) := by
  have norm_equal : ‖z.val‖ = dist source (R.cutCompletionProjection injective z) :=
    R.norm_eq_projection_distance injective (PolygonalPoint.toSubtype z)
  rw [R.cutOrigin_edist, norm_equal]
  exact (edist_dist _ _).symm

omit [CompactSpace X] in
theorem cutRadial_source_vector_injective
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    Function.Injective R.cutPoint := by
  intro p q equal
  exact injective (congrArg PolygonalPoint.val equal)

end Unfoldings.SourceFrame
