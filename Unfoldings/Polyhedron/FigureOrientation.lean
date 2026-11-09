module

public import Unfoldings.Polyhedron.FigureRadialCover
public import Unfoldings.Geometry.AdjacentBoundaryEdges
public import Unfoldings.Geometry.AffineOrientation

/-!
# Consistent radial orientation of the actual figure polygon

Consecutive central triangles keep the same signed-area sign, including
straight boundary subdivisions. Induction along the actual chain makes
this sign global; any rigid change of planar coordinates preserves the
relative signs.
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

theorem linkPolygon_adjacent_orient_product
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    0 < orient (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) 0 *
      orient (V.linkPolygon c (finRotate (n + 1) i))
        (V.linkPolygon c (finRotate (n + 1) (finRotate (n + 1) i))) 0 := by
  have different : i ≠ finRotate (n + 1) i := fun equal =>
    V.linkPolygon_nondegenerate c closes i (congrArg (V.linkPolygon c) equal)
  exact orient_mul_pos_of_adjacent_boundary_edges V.convex_carrier
    V.compact_carrier.isClosed V.zero_mem_interior
    (V.linkPolygon_nondegenerate c closes i)
    (V.linkPolygon_nondegenerate c closes (finRotate (n + 1) i))
    (P.linkPolygon_edge_subset_frontier V c closes i)
    (P.linkPolygon_edge_subset_frontier V c closes (finRotate (n + 1) i))
    (V.linkPolygon_disjoint_open_edges c P.embedded closes _ _ different)
    (V.linkPolygon_disjoint_open_edges c P.embedded closes _ _ different.symm)

theorem linkPolygon_orient_sign
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    (0 < orient (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) 0) ↔
      0 < orient (V.linkPolygon c 0) (V.linkPolygon c (finRotate (n + 1) 0)) 0 := by
  refine Fin.induction Iff.rfl (fun k previous => ?_) i
  have adjacent := P.linkPolygon_adjacent_orient_product V c closes k.castSucc
  have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
  rw [rotated] at adjacent previous
  exact (pos_iff_pos_of_mul_pos adjacent).symm.trans previous

theorem linkPolygon_orient_product
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i j : Fin (n + 1)) :
    0 < orient (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) 0 *
      orient (V.linkPolygon c j) (V.linkPolygon c (finRotate (n + 1) j)) 0 := by
  have ane := orient_ne_zero_of_boundary_segment V.convex_carrier V.compact_carrier.isClosed
    V.zero_mem_interior (V.linkPolygon_nondegenerate c closes i)
    (P.linkPolygon_edge_subset_frontier V c closes i)
  have bne := orient_ne_zero_of_boundary_segment V.convex_carrier V.compact_carrier.isClosed
    V.zero_mem_interior (V.linkPolygon_nondegenerate c closes j)
    (P.linkPolygon_edge_subset_frontier V c closes j)
  by_cases positive : 0 < orient (V.linkPolygon c 0)
      (V.linkPolygon c (finRotate (n + 1) 0)) 0
  · exact mul_pos ((P.linkPolygon_orient_sign V c closes i).mpr positive)
      ((P.linkPolygon_orient_sign V c closes j).mpr positive)
  · have first : orient (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) 0 < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun hi =>
        positive ((P.linkPolygon_orient_sign V c closes i).mp hi))) ane
    have second : orient (V.linkPolygon c j) (V.linkPolygon c (finRotate (n + 1) j)) 0 < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun hj =>
        positive ((P.linkPolygon_orient_sign V c closes j).mp hj))) bne
    exact mul_pos_of_neg_of_neg first second

end Unfoldings.SpatialFolding.ConvexBoundary
