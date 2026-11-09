module

public import Unfoldings.Polyhedron.FigureCenter
public import Unfoldings.Geometry.FrontierRays

/-!
# Coverage and separation of the actual central radial sectors

Radial cones over the closed polygon edges cover every nonzero planar point.
An open radial cone misses every other closed radial cone. Both conclusions
follow from the actual convex frontier and its derived edge incidence, without
assuming that the angular fan makes one turn.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

include P

theorem linkPolygon_edge_subset_frontier
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    segment ℝ (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) ⊆
      frontier V.carrier := by
  have edge := P.figure_germ_segment_subset_boundary V (c.point i)
  rw [V.germPoint_chain_rotates c closes i] at edge
  exact edge

theorem linkPolygon_positiveRadial_cover
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    (⋃ i, positiveRadialHull (segment ℝ (V.linkPolygon c i)
      (V.linkPolygon c (finRotate (n + 1) i)))) = ({0} : Set Plane)ᶜ := by
  have boundary : (⋃ i, segment ℝ (V.linkPolygon c i)
      (V.linkPolygon c (finRotate (n + 1) i))) = frontier V.carrier := by
    simpa only [Polygon.boundary, Polygon.edgeSet, affineSegment_eq_segment] using
      P.linkPolygon_boundary V c closes covers
  rw [← positiveRadialHull_iUnion, boundary]
  exact positiveRadialHull_frontier V.convex_carrier V.zero_mem_interior
    V.compact_carrier.isBounded

theorem linkPolygon_positiveRadial_disjoint
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    {i j : Fin (n + 1)} (different : i ≠ j) :
    Disjoint (positiveRadialHull (openSegment ℝ (V.linkPolygon c i)
      (V.linkPolygon c (finRotate (n + 1) i))))
      (positiveRadialHull (segment ℝ (V.linkPolygon c j)
        (V.linkPolygon c (finRotate (n + 1) j)))) :=
  disjoint_positiveRadialHulls_of_frontier V.convex_carrier V.zero_mem_interior
    ((openSegment_subset_segment ℝ _ _).trans (P.linkPolygon_edge_subset_frontier V c closes i))
    (P.linkPolygon_edge_subset_frontier V c closes j)
    (V.linkPolygon_disjoint_open_edges c P.embedded closes i j different)

end Unfoldings.SpatialFolding.ConvexBoundary
