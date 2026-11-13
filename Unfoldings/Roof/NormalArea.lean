module

public import Unfoldings.Roof.NormalImage
public import Unfoldings.Geometry.ConvexPacking
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A uniform area budget for all planar normal polygons

Their actual disjoint interiors and common gnomonic disk give a total area
bound independent of vertex count. Degenerate polygons and boundary contacts
are included. This is planar normal-image area, not yet intrinsic curvature.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The entire finite normal image fits in the area of one tilt-controlled disk. -/
theorem normalPolygon_area_budget {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) :
    (∑ v : C.Vertex Set.univ, volume (K.normalPolygon v)) ≤
      ENNReal.ofReal (Real.sqrt (1 - c ^ 2) / c) ^ 2 * ENNReal.ofReal Real.pi := by
  have budget := sum_measure_convex_le volume K.normalPolygon
    (fun _ => convex_convexHull ℝ _)
    (fun _ _ different => K.normalPolygons_nonoverlapping different)
    (Metric.closedBall (0 : Plane) (Real.sqrt (1 - c ^ 2) / c))
    (K.normalPolygon_subset_disk positive height)
  simpa only [EuclideanSpace.volume_closedBall_fin_two] using budget

end Unfoldings.ConvexRoof
