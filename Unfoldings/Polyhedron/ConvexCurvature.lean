module

public import Unfoldings.Polyhedron.Closedness
public import Unfoldings.Polyhedron.ExtremeCurvature

/-! Curvature and geodesic avoidance at all actual convex-boundary extreme vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem extreme_vertex_totalAngle_lt_two_pi (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    C.totalAngle Set.univ v < 2 * Real.pi :=
  P.totalAngle_lt_two_pi_of_extreme v (P.not_isBoundaryVertex v) extreme

theorem extreme_vertex_iff_positive_curvature (v : C.Vertex Set.univ) :
    F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ ↔
      C.totalAngle Set.univ v < 2 * Real.pi :=
  P.mem_extremePoints_iff_totalAngle_lt_two_pi v (P.not_isBoundaryVertex v)

theorem geodesic_ne_extreme (v : C.Vertex Set.univ)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (distinct : a ≠ b) (t : unitInterval) (time : t ∈ Set.Ioo (0 : unitInterval) 1) :
    p t ≠ C.vertexPoint Set.univ v :=
  P.geodesic_ne_extreme_vertex v (P.not_isBoundaryVertex v) extreme geodesic distinct t time

end Unfoldings.SpatialFolding.ConvexBoundary
