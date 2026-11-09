module

public import Unfoldings.Polyhedron.Chords
public import Unfoldings.Geometry.BoundaryChord
public import Unfoldings.Cone.VertexAvoidance
public import Mathlib.Analysis.Convex.Extreme

/-!
# Positive-curvature vertices are spatial extreme points

A spatial boundary chord has exact intrinsic length. If a triangulation
vertex lies strictly between two body points, convexity forces their whole
chord onto the boundary. Its intrinsic shortest path passes through that
vertex, contradicting the proved positive-curvature avoidance theorem.

Flat subdivision vertices remain permitted. The upper angle bound from
convexity is a separate theorem, not an input to this argument.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem positive_vertex_mem_extremePoints (v : C.Vertex Set.univ)
    (interior : ¬ C.IsBoundaryVertex Set.univ v)
    (positive_curvature : C.totalAngle Set.univ v < 2 * Real.pi) :
    F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ := by
  let z := F.toSpace Set.univ (C.vertexPoint Set.univ v)
  have surface : z ∈ F.surface := (F.range_toSpace Set.univ).le ⟨C.vertexPoint Set.univ v, rfl⟩
  have boundary : z ∈ frontier F.vertexHull := by rw [← P.boundary]; exact surface
  apply mem_extremePoints_iff_left.mpr
  refine ⟨F.surface_subset_vertexHull surface, ?_⟩
  intro x hx y hy between
  by_contra nontrivial
  have distinct_xy : x ≠ y := by
    intro same
    have z_eq_y : z = y := by
      simpa only [same, openSegment_same, Set.mem_singleton_iff] using between
    exact nontrivial (same.trans z_eq_y.symm)
  have spatial_chord : segment ℝ x y ⊆ F.surface := by
    rw [P.boundary]
    exact segment_subset_frontier_of_openSegment_mem F.convex_vertexHull hx hy between boundary
  obtain ⟨a, ha⟩ := (F.range_toSpace Set.univ).ge (spatial_chord (left_mem_segment ℝ _ _))
  obtain ⟨b, hb⟩ := (F.range_toSpace Set.univ).ge (spatial_chord (right_mem_segment ℝ _ _))
  have distinct : a ≠ b := by
    intro same
    exact distinct_xy (ha.symm.trans ((congrArg (F.toSpace Set.univ) same).trans hb))
  have chord : segment ℝ (F.toSpace Set.univ a) (F.toSpace Set.univ b) ⊆ F.surface := by
    rw [ha, hb]
    exact spatial_chord
  obtain ⟨p, geodesic⟩ := P.exists_geodesic a b
  rw [openSegment_eq_image_lineMap] at between
  obtain ⟨t, time, image⟩ := between
  let u : unitInterval := ⟨t, time.1.le, time.2.le⟩
  have through : p u = C.vertexPoint Set.univ v := by
    apply P.embedded
    have trace := P.geodesic_spatial_eq_lineMap chord geodesic u
    rw [ha, hb] at trace
    exact trace.trans image
  exact F.geodesic_ne_positive_vertex Set.univ v interior positive_curvature
    geodesic distinct u ⟨time.1, time.2⟩ through

/-- At a nonextreme subdivision vertex, the missing convex upper bound will
force equality with a full turn, rather than strict positive curvature. -/
theorem two_pi_le_totalAngle_of_not_extreme (v : C.Vertex Set.univ)
    (interior : ¬ C.IsBoundaryVertex Set.univ v)
    (not_extreme :
      F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    2 * Real.pi ≤ C.totalAngle Set.univ v :=
  le_of_not_gt (fun small => not_extreme (P.positive_vertex_mem_extremePoints v interior small))

end Unfoldings.SpatialFolding.ConvexBoundary
