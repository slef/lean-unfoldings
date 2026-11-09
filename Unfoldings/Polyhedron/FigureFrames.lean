module

public import Unfoldings.Polyhedron.FigureOrientation
public import Unfoldings.Cone.CornerSector

/-! Constructed rigid frames for the actual central triangles of a vertex figure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

def figureCentralTriangle
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) : Triangle where
  vertex := ![0, V.linkPolygon c i, V.linkPolygon c (finRotate (n + 1) i)]
  nondegenerate := by
    change orient 0 (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) ≠ 0
    rw [← orient_cyclic]
    exact orient_ne_zero_of_boundary_segment V.convex_carrier V.compact_carrier.isClosed
      V.zero_mem_interior (V.linkPolygon_nondegenerate c closes i)
      (P.linkPolygon_edge_subset_frontier V c closes i)

@[simp] theorem figureCentralTriangle_angle
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    (P.figureCentralTriangle V c closes i).cornerAngle 0 =
      (P.figureCentralFan V c closes).angle i := rfl

def figureCentralFrame
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) : (P.figureCentralTriangle V c closes i).CornerFrame 0 :=
  (P.figureCentralTriangle V c closes i).cornerFrame 0

@[simp] theorem figureCentralFrame_zero
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) : (P.figureCentralFrame V c closes i).place 0 = 0 :=
  (P.figureCentralFrame V c closes i).apex

theorem figureCentralFrame_first
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    (P.figureCentralFrame V c closes i).place (V.linkPolygon c i) =
      (‖V.linkPolygon c i‖ : ℂ) := by
  have first := (P.figureCentralFrame V c closes i).first
  change (P.figureCentralFrame V c closes i).place (V.linkPolygon c i) =
    (dist 0 (V.linkPolygon c i) : ℂ) at first
  simpa only [dist_zero_left] using first

theorem figureCentralFrame_second
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    (P.figureCentralFrame V c closes i).place (V.linkPolygon c (finRotate (n + 1) i)) =
      (‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℂ) *
        polarRay ((P.figureCentralFan V c closes).angle i) := by
  have second := (P.figureCentralFrame V c closes i).second_polar
  change (P.figureCentralFrame V c closes i).place (V.linkPolygon c (finRotate (n + 1) i)) =
    (dist 0 (V.linkPolygon c (finRotate (n + 1) i)) : ℂ) *
      polarRay ((P.figureCentralFan V c closes).angle i) at second
  simpa only [dist_zero_left] using second

end Unfoldings.SpatialFolding.ConvexBoundary
