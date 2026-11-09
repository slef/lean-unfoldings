module

public import Unfoldings.Polyhedron.FigureAngleSum
public import Unfoldings.Polyhedron.ExtremeVertices

/-!
# Extreme vertices are exactly the positive-curvature interior vertices

Both directions are derived from convex spatial geometry and the actual
intrinsic metric. Consequently nonconstant intrinsic geodesics avoid all
interior spatial extreme vertices at interior parameter times.

The full upper angle bound and flatness of nonextreme subdivision vertices
remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem mem_extremePoints_iff_totalAngle_lt_two_pi (v : C.Vertex Set.univ)
    (interior : ¬ C.IsBoundaryVertex Set.univ v) :
    F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ ↔
      C.totalAngle Set.univ v < 2 * Real.pi :=
  ⟨P.totalAngle_lt_two_pi_of_extreme v interior, P.positive_vertex_mem_extremePoints v interior⟩

theorem geodesic_ne_extreme_vertex (v : C.Vertex Set.univ)
    (interior : ¬ C.IsBoundaryVertex Set.univ v)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (distinct : a ≠ b) (t : unitInterval) (time : t ∈ Set.Ioo (0 : unitInterval) 1) :
    p t ≠ C.vertexPoint Set.univ v :=
  F.geodesic_ne_positive_vertex Set.univ v interior
    (P.totalAngle_lt_two_pi_of_extreme v interior extreme) geodesic distinct t time

end Unfoldings.SpatialFolding.ConvexBoundary
