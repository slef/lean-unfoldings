module

public import Unfoldings.Polyhedron.NonextremeRegular
public import Unfoldings.Polyhedron.RegularPoints
public import Unfoldings.Polyhedron.ConvexCurvature

/-! Interior points of nonconstant convex-boundary geodesics are Euclidean. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem isRegularPoint_of_ne_extreme_vertices (x : C.Realization Set.univ)
    (outside : ∀ v : C.Vertex Set.univ,
      F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ →
        x ≠ C.vertexPoint Set.univ v) : C.IsRegularPoint Set.univ x := by
  by_cases vertex : ∃ v, x = C.vertexPoint Set.univ v
  · obtain ⟨v, rfl⟩ := vertex
    apply P.isRegularPoint_nonextreme_vertex v
    intro extreme
    exact outside v extreme rfl
  · exact P.isRegularPoint_of_not_vertex x (fun v equal => vertex ⟨v, equal⟩)

theorem geodesic_isRegularPoint {a b : C.Realization Set.univ} {p : Path a b}
    (geodesic : p.IsGeodesic) (distinct : a ≠ b) (t : unitInterval)
    (time : t ∈ Set.Ioo (0 : unitInterval) 1) : C.IsRegularPoint Set.univ (p t) :=
  P.isRegularPoint_of_ne_extreme_vertices (p t)
    (fun v extreme => P.geodesic_ne_extreme v extreme geodesic distinct t time)

theorem geodesics_eq_of_initial_interval
    {a b c d : C.Realization Set.univ} {p : Path a b} {q : Path c d}
    (geodesic : p.IsGeodesic) (other : q.IsGeodesic) (distinct : a ≠ b)
    (initial : ∃ ε : unitInterval, 0 < ε ∧ ∀ t ≤ ε, p t = q t) :
    ∀ t, p t = q t :=
  C.geodesics_eq_of_initial_interval Set.univ geodesic other initial
    (fun t time => P.geodesic_isRegularPoint geodesic distinct t time)

end Unfoldings.SpatialFolding.ConvexBoundary
