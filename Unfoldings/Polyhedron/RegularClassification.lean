module

public import Unfoldings.Metric.RegularGeodesic
public import Unfoldings.Polyhedron.GeodesicRegularity

/-! Actual regular points are exactly the complement of spatial extreme vertex points. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem regular_vertex_not_extreme (v : C.Vertex Set.univ)
    (regular : C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v)) :
    F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ := by
  intro extreme
  obtain ⟨a, b, p, geodesic, distinct, t, time, through⟩ := regular.exists_geodesic_through
  exact P.geodesic_ne_extreme v extreme geodesic distinct t time through

theorem isRegularPoint_iff_ne_extreme_vertices (x : C.Realization Set.univ) :
    C.IsRegularPoint Set.univ x ↔ ∀ v : C.Vertex Set.univ,
      F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ →
        x ≠ C.vertexPoint Set.univ v := by
  constructor
  · intro regular v extreme equal
    subst x
    exact P.regular_vertex_not_extreme v regular extreme
  · exact P.isRegularPoint_of_ne_extreme_vertices x

end Unfoldings.SpatialFolding.ConvexBoundary
