module

public import Unfoldings.Polyhedron.FigurePolygon
public import Unfoldings.Geometry.ConvexBoundaryEdges
public import Unfoldings.Geometry.ConvexBoundaryRays
public import Unfoldings.Cone.AngularFan

/-!
# The central triangles of the actual convex vertex figure

Zero is an actual interior center of the constructed figure. Supporting
edge functionals prove that every triangle from this center to a boundary
edge is noncollinear, giving genuine positive sector angles below pi.
Distinct listed endpoints cannot lie on the same positive radial ray.
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

theorem linkPolygon_center_not_collinear
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    ¬ Collinear ℝ ({V.linkPolygon c i, 0,
      V.linkPolygon c (finRotate (n + 1) i)} : Set Plane) := by
  have edge := P.figure_germ_segment_subset_boundary V (c.point i)
  rw [V.germPoint_chain_rotates c closes i] at edge
  exact not_collinear_of_boundary_segment V.convex_carrier V.compact_carrier.isClosed
    V.zero_mem_interior (V.linkPolygon_nondegenerate c closes i) edge

def figureCentralFan
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    AngularFan n where
  angle i := EuclideanGeometry.angle (V.linkPolygon c i) 0
    (V.linkPolygon c (finRotate (n + 1) i))
  positive i := EuclideanGeometry.angle_pos_of_not_collinear
    (P.linkPolygon_center_not_collinear V c closes i)
  small i := EuclideanGeometry.angle_lt_pi_of_not_collinear
    (P.linkPolygon_center_not_collinear V c closes i)

theorem linkPolygon_ray_injective
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    {i j : Fin (n + 1)} {t : ℝ} (nonnegative : 0 ≤ t)
    (equal : V.linkPolygon c j = t • V.linkPolygon c i) : i = j := by
  apply V.germPoint_chain_injective c P.embedded closes
  exact eq_of_frontier_eq_nonnegative_smul V.convex_carrier V.zero_mem_interior
    (P.figure_germPoint_mem_frontier V (c.point i))
    (P.figure_germPoint_mem_frontier V (c.point j)) nonnegative equal |>.symm

end Unfoldings.SpatialFolding.ConvexBoundary
